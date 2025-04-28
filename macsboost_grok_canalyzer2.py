import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import tkinter.font as tkfont
import threading
import queue
import can
import configparser
import csv
import time
from datetime import datetime
import serial.tools.list_ports
import serial
import struct

try:
    import cantools
except ImportError:
    cantools = None
try:
    import matplotlib
    matplotlib.use('TkAgg')
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
    from matplotlib.figure import Figure
except ImportError:
    plt = None
    Figure = None

class CANApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("CAN Bus Analyzer")
        self.geometry("1200x800")
        self.protocol("WM_DELETE_WINDOW", self.on_closing)

        # Initialize variables
        self.bus = None
        self.running = False
        self.log_file = None
        self.log_writer = None
        self.message_queue = queue.Queue()
        self.last_data = {}
        self.id_stats = {}
        self.periodic_task_id = None
        self.messages = {}
        self.message_history = {}
        self.start_time = time.time()
        self.last_message_timestamp = None
        self.paused = False
        self.filter_ids = set()
        self.dbc = None
        self.available_adapters = ['slcan', 'socketcan', 'pcan', 'usb2can', 'ixxat', 'kvaser']
        self.serial_adapters = ['slcan', 'usb2can']
        self.available_baudrates = ['9600', '19200', '38400', '57600', '115200', '921600']
        self.available_bitrates = ['125000', '250000', '500000', '1000000']
        self.available_data_bitrates = ['2000000', '4000000', '8000000']
        self.highlighted_rows = {}
        self.max_messages = 500
        self.highlight_mode = 'Message Change'
        self.serial_number = "Unknown"
        self.message_count = 0
        self.message_rate = 0.0
        self.bus_load = 0.0
        self.last_stats_update = time.time()
        self.display_mode = {}
        self.endian_var = tk.BooleanVar(value=True)
        self.highlight_changes_var = tk.BooleanVar(value=True)
        self.can_error_count = 0
        self.send_periodic_var = tk.BooleanVar(value=False)
        self.extended_id_var = tk.BooleanVar(value=False)
        self.can_fd_var = tk.BooleanVar(value=False)

        # Load configuration
        self.load_config()

        # Build GUI
        self.create_gui()

        # Schedule periodic updates
        self.check_queue()
        self.schedule_stats_update()

    def load_config(self):
        self.cfg = configparser.ConfigParser()
        default_port = self.detect_canable_port() or '/dev/ttyACM0'
        if not self.cfg.read('.canconfig'):
            self.cfg['Interface'] = {
                'bustype': 'slcan',
                'port': default_port,
                'channel': 'can0',
                'bitrate': '500000',
                'baudrate': '115200',
                'data_bitrate': '2000000',
                'extended_id': 'False',
                'can_fd': 'False'
            }
            self.cfg['Logging'] = {'log_file': 'can_log.csv'}
            self.cfg['Display'] = {
                'time_mode': 'Timestamp',
                'dark_mode': 'False'
            }
            self.save_config()
        else:
            if 'Interface' not in self.cfg:
                self.cfg['Interface'] = {
                    'bustype': 'slcan',
                    'port': default_port,
                    'channel': 'can0',
                    'bitrate': '500000',
                    'baudrate': '115200',
                    'data_bitrate': '2000000',
                    'extended_id': 'False',
                    'can_fd': 'False'
                }
            if 'Logging' not in self.cfg:
                self.cfg['Logging'] = {'log_file': 'can_log.csv'}
            if 'Display' not in self.cfg:
                self.cfg['Display'] = {
                    'time_mode': 'Timestamp',
                    'dark_mode': 'False'
                }
            self.save_config()
        self.time_mode = self.cfg['Display'].get('time_mode', 'Timestamp')
        self.dark_mode = self.cfg.getboolean('Display', 'dark_mode', fallback=False)
        self.extended_id_var.set(self.cfg.getboolean('Interface', 'extended_id', fallback=False))
        self.can_fd_var.set(self.cfg.getboolean('Interface', 'can_fd', fallback=False))

    def save_config(self):
        with open('.canconfig', 'w') as configfile:
            self.cfg.write(configfile)

    def detect_canable_port(self):
        ports = serial.tools.list_ports.comports()
        for port in ports:
            if 'Canable' in port.description or 'ttyACM' in port.device or 'ttyUSB' in port.device or 'cu.usbmodem' in port.device:
                return port.device
        return None

    def get_serial_number(self, port, baudrate=115200):
        try:
            with serial.Serial(port, baudrate, timeout=1) as ser:
                ser.write(b'N\r')
                response = ser.read(100).decode('ascii', errors='ignore').strip()
                if response.startswith('N') or response.startswith('T'):
                    return response[:16]
        except Exception:
            pass
        return "Unknown"

    def get_serial_ports(self):
        return [port.device for port in serial.tools.list_ports.comports()]

    def create_gui(self):
        font_candidates = [
            ("Courier", 11), ("Menlo", 11), ("Inconsolata", 11),
            ("Courier New", 11), ("DejaVu Sans Mono", 11),
            ("Monaco", 11), ("Consolas", 11)
        ]
        self.mono_font = ("Courier", 11)
        selected_font = "Courier"
        for font_name, size in font_candidates:
            try:
                font_obj = tkfont.Font(family=font_name, size=size)
                self.mono_font = (font_name, size)
                selected_font = font_name
                break
            except:
                pass

        port = self.cfg['Interface'].get('port', '/dev/ttyACM0')
        baudrate = int(self.cfg['Interface'].get('baudrate', '115200'))
        self.serial_number = self.get_serial_number(port, baudrate)

        menu_bar = tk.Menu(self)
        self.config(menu=menu_bar)
        file_menu = tk.Menu(menu_bar, tearoff=0)
        menu_bar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="Start Logging", command=self.start_logging)
        file_menu.add_command(label="Stop Logging", command=self.stop_logging)
        file_menu.add_command(label="Load DBC", command=self.load_dbc)
        file_menu.add_command(label="Clear Treeview", command=self.clear_treeview)
        file_menu.add_command(label="Exit", command=self.on_closing)
        settings_menu = tk.Menu(menu_bar, tearoff=0)
        menu_bar.add_cascade(label="Settings", menu=settings_menu)
        settings_menu.add_command(label="Interface Settings", command=self.open_interface_settings)
        tools_menu = tk.Menu(menu_bar, tearoff=0)
        menu_bar.add_cascade(label="Tools", menu=tools_menu)
        tools_menu.add_command(label="Diff Selected Messages", command=self.diff_selected)
        tools_menu.add_command(label="Plot Signals", command=self.plot_signals)
        tools_menu.add_command(label="Resend Selected Message", command=self.resend_selected)
        tools_menu.add_command(label="Analyze Bytes", command=self.analyze_bytes)

        toolbar = ttk.Frame(self)
        toolbar.pack(side="top", fill="x", padx=5, pady=5)
        ttk.Button(toolbar, text="Start", command=self.start_can).pack(side="left", padx=2)
        ttk.Button(toolbar, text="Stop", command=self.stop_can).pack(side="left", padx=2)
        self.pause_btn = ttk.Button(toolbar, text="Pause", command=self.toggle_pause)
        self.pause_btn.pack(side="left", padx=2)
        ttk.Button(toolbar, text="Reset Stats", command=self.reset_stats).pack(side="left", padx=2)
        self.connection_indicator = tk.Canvas(toolbar, width=20, height=20, bd=0, highlightthickness=0)
        self.connection_indicator.pack(side="left", padx=5)
        self.connection_indicator.create_oval(2, 2, 18, 18, fill='red', tags='indicator')
        ttk.Label(toolbar, text="Filter IDs (hex, comma-separated):").pack(side="left", padx=2)
        self.filter_entry = ttk.Entry(toolbar, width=15)
        self.filter_entry.pack(side="left", padx=2)
        self.filter_entry.bind("<Return>", self.apply_filter)
        ttk.Checkbutton(toolbar, text="Highlight Changes", variable=self.highlight_changes_var).pack(side="left", padx=2)
        ttk.Checkbutton(toolbar, text="Big Endian", variable=self.endian_var, command=self.update_all_display_columns).pack(side="left", padx=2)
        ttk.Checkbutton(toolbar, text="29-bit ID", variable=self.extended_id_var, command=self.update_send_labels).pack(side="left", padx=2)
        ttk.Checkbutton(toolbar, text="CAN FD", variable=self.can_fd_var, command=self.update_send_labels).pack(side="left", padx=2)

        info_frame = ttk.Frame(self)
        info_frame.pack(side="top", fill="x", padx=5, pady=2)
        self.serial_label = ttk.Label(info_frame, text=f"Serial: {self.serial_number}", width=28)
        self.serial_label.pack(side="left", padx=5)
        self.interface_label = ttk.Label(info_frame, text="Interface: Disconnected")
        self.interface_label.pack(side="left", padx=5)
        self.stats_label = ttk.Label(info_frame, text="Baud: N/A | Msg/s: 0.0 | Bus Load: 0.0%")
        self.stats_label.pack(side="left", padx=5)
        style = ttk.Style()
        actual_font = style.lookup("Mono.Treeview", "font", default=selected_font)
        self.font_debug_label = ttk.Label(info_frame, text=f"Font: {actual_font or selected_font} {self.mono_font[1]}")
        self.font_debug_label.pack(side="left", padx=5)

        main_pane = ttk.PanedWindow(self, orient="horizontal")
        main_pane.pack(fill="both", expand=True, padx=5, pady=5)

        message_frame = ttk.LabelFrame(main_pane, text="Messages")
        main_pane.add(message_frame, weight=3)
        self.message_tree = ttk.Treeview(
            message_frame,
            columns=("Time", "ID", "Data", "Display", "Direction"),
            show="headings",
            selectmode="extended",
            style="Mono.Treeview"
        )
        style.theme_use('clam')
        style.configure("Mono.Treeview", font=self.mono_font, rowheight=int(self.mono_font[1] * 2))
        self.message_tree.heading("Time", text="Time")
        self.message_tree.heading("ID", text="ID")
        self.message_tree.heading("Data", text="Data")
        self.message_tree.heading("Display", text="Display", command=self.cycle_ascii_mode)
        self.message_tree.heading("Direction", text="Dir")
        self.message_tree.column("Time", width=150)
        self.message_tree.column("ID", width=100)
        self.message_tree.column("Data", width=200)
        self.message_tree.column("Display", width=200)
        self.message_tree.column("Direction", width=50)
        self.message_tree.pack(fill="both", expand=True)
        self.update_highlight_tags()
        self.message_tree.bind("<Command-c>", self.copy_selection)
        self.message_tree.bind("<Button-2>", self.show_context_menu)
        self.message_tree.bind("<Button-3>", self.show_context_menu)

        right_frame = ttk.Frame(main_pane)
        main_pane.add(right_frame, weight=1)

        stats_frame = ttk.LabelFrame(right_frame, text="Statistics")
        stats_frame.pack(fill="both", expand=True, padx=5, pady=5)
        self.stats_tree = ttk.Treeview(
            stats_frame,
            columns=("ID", "Count", "Last Time", "Frequency"),
            show="headings",
            style="Mono.Treeview"
        )
        self.stats_tree.heading("ID", text="ID")
        self.stats_tree.heading("Count", text="Count")
        self.stats_tree.heading("Last Time", text="Last Time")
        self.stats_tree.heading("Frequency", text="Freq (Hz)")
        self.stats_tree.column("ID", width=100)
        self.stats_tree.column("Count", width=50)
        self.stats_tree.column("Last Time", width=100)
        self.stats_tree.column("Frequency", width=100)
        self.stats_tree.pack(fill="both", expand=True)

        send_frame = ttk.LabelFrame(right_frame, text="Send Message")
        send_frame.pack(fill="x", padx=5, pady=5)
        self.id_label = ttk.Label(send_frame, text="ID (hex, 0-7FF):")
        self.id_label.grid(row=0, column=0, padx=2, pady=2)
        self.id_entry = ttk.Entry(send_frame, width=10)
        self.id_entry.insert(0, "123")
        self.id_entry.grid(row=0, column=1, padx=2, pady=2)
        self.data_label = ttk.Label(send_frame, text="Data (hex, 0-8 bytes):")
        self.data_label.grid(row=1, column=0, padx=2, pady=2)
        self.data_entry = ttk.Entry(send_frame, width=20)
        self.data_entry.insert(0, "01 02 03 04")
        self.data_entry.grid(row=1, column=1, padx=2, pady=2)
        self.data_entry.bind("<Return>", self.format_data_entry)
        self.send_once_btn = ttk.Button(send_frame, text="Send Once", command=self.send_once)
        self.send_once_btn.grid(row=2, column=0, padx=2, pady=2)
        self.send_periodic_check = ttk.Checkbutton(
            send_frame,
            text="Send Periodically",
            variable=self.send_periodic_var,
            command=self.toggle_periodic
        )
        self.send_periodic_check.grid(row=2, column=1, padx=2, pady=2)
        ttk.Label(send_frame, text="Interval (ms):").grid(row=3, column=0, padx=2, pady=2)
        self.interval_entry = ttk.Entry(send_frame, width=10)
        self.interval_entry.insert(0, "1000")
        self.interval_entry.grid(row=3, column=1, padx=2, pady=2)

        # Update send labels initially
        self.update_send_labels()

        self.status_bar = ttk.Label(self, text="Disconnected", relief="sunken")
        self.status_bar.pack(side="bottom", fill="x")

        self.context_menu = tk.Menu(self, tearoff=0)
        self.context_menu.add_command(label="Copy", command=self.copy_selection)
        self.context_menu.add_command(label="Decode 8-bit", command=lambda: self.decode_selection(8))
        self.context_menu.add_command(label="Decode 16-bit BE", command=lambda: self.decode_selection(16, 'big'))
        self.context_menu.add_command(label="Decode 16-bit LE", command=lambda: self.decode_selection(16, 'little'))
        self.context_menu.add_command(label="Decode 32-bit BE", command=lambda: self.decode_selection(32, 'big'))
        self.context_menu.add_command(label="Decode 32-bit LE", command=lambda: self.decode_selection(32, 'little'))

        if self.dark_mode:
            self.toggle_dark_mode()

        self.update_status_bar()

    def update_send_labels(self):
        id_label = "ID (hex, 0-1FFFFFFF):" if self.extended_id_var.get() else "ID (hex, 0-7FF):"
        data_label = "Data (hex, 0-64 bytes):" if self.can_fd_var.get() else "Data (hex, 0-8 bytes):"
        self.id_label.config(text=id_label)
        self.data_label.config(text=data_label)

    def update_highlight_tags(self):
        steps = 8
        shades = []
        if self.dark_mode:
            start_rgb = (102, 102, 102)
            end_rgb = (51, 51, 51)
        else:
            start_rgb = (230, 230, 230)
            end_rgb = (255, 255, 255)
        for step in range(steps):
            r = int(start_rgb[0] - (start_rgb[0] - end_rgb[0]) * step / (steps - 1))
            g = int(start_rgb[1] - (start_rgb[1] - end_rgb[1]) * step / (steps - 1))
            b = int(start_rgb[2] - (start_rgb[2] - end_rgb[2]) * step / (steps - 1))
            hex_color = f"#{r:02X}{g:02X}{b:02X}"
            shades.append(hex_color)
        for i in range(1, steps + 1):
            self.message_tree.tag_configure(f'changed{i}', background=shades[i-1])
        self.update_idletasks()

    def format_data_entry(self, event):
        text = self.data_entry.get().replace(' ', '').lower()
        max_bytes = 64 if self.can_fd_var.get() else 8
        if not text:
            formatted = ' '.join(['00'] * max_bytes)
        else:
            if not all(c in '0123456789abcdef' for c in text):
                messagebox.showerror("Error", "Data must contain only hex digits (0-9, a-f)")
                return
            if len(text) > max_bytes * 2:
                messagebox.showerror("Error", f"Data must be at most {max_bytes} bytes ({max_bytes * 2} hex digits)")
                return
            text = text.ljust(max_bytes * 2, '0')
            formatted = ' '.join(text[i:i+2] for i in range(0, len(text), 2))
        self.data_entry.delete(0, tk.END)
        self.data_entry.insert(0, formatted)

    def validate_send_inputs(self):
        try:
            can_id = int(self.id_entry.get(), 16)
            max_id = 0x1FFFFFFF if self.extended_id_var.get() else 0x7FF
            if can_id < 0 or can_id > max_id:
                raise ValueError(f"CAN ID must be between 0 and {hex(max_id)}")
            data_text = self.data_entry.get().replace(' ', '')
            max_bytes = 64 if self.can_fd_var.get() else 8
            if not data_text:
                data = bytes(max_bytes)
            else:
                if not all(c in '0123456789ABCDEFabcdef' for c in data_text):
                    raise ValueError("Data must contain only hex digits")
                if len(data_text) % 2 != 0:
                    raise ValueError("Data must have even number of hex digits")
                data = bytes.fromhex(data_text)
            if len(data) > max_bytes:
                raise ValueError(f"Data must be 0 to {max_bytes} bytes")
            interval = float(self.interval_entry.get())
            if interval <= 0:
                raise ValueError("Interval must be positive")
            return can_id, data, interval
        except ValueError as e:
            messagebox.showerror("Error", f"Invalid input: {e}")
            return None

    def cycle_ascii_mode(self):
        selected = self.message_tree.selection()
        if not selected:
            return
        item = self.message_tree.item(selected[0])
        can_id = item['values'][1]
        current_mode = self.display_mode.get(can_id, 'binary')
        modes = ['binary', 'dec8', 'dec16', 'decoded']
        next_mode = modes[(modes.index(current_mode) + 1) % len(modes)]
        self.display_mode[can_id] = next_mode
        self.update_display_column(can_id, item)

    def update_display_column(self, can_id, item):
        data = item['values'][2].split()
        mode = self.display_mode.get(can_id, 'binary')
        endian = 'big' if self.endian_var.get() else 'little'

        if mode == 'binary':
            binary_data = ' '.join(format(int(b, 16), '08b').replace('0', '0').replace('1', '1') for b in data)
            display_data = binary_data
        elif mode == 'dec8':
            display_data = ' '.join(f"{int(b, 16):d}" for b in data)
        elif mode == 'dec16':
            if len(data) % 2 != 0:
                display_data = "N/A (Odd bytes)"
            else:
                pairs = [data[i:i+2] for i in range(0, len(data), 2)]
                values = []
                for pair in pairs:
                    bytes_data = bytes([int(pair[0], 16), int(pair[1], 16)])
                    value = struct.unpack('>H' if endian == 'big' else '<H', bytes_data)[0]
                    values.append(str(value))
                display_data = ' '.join(values)
        else:
            if self.dbc and cantools:
                try:
                    message = self.dbc.get_message_by_frame_id(int(can_id, 16))
                    decoded_dict = message.decode(bytes([int(b, 16) for b in data]))
                    display_data = ', '.join(f"{k}: {v}" for k, v in decoded_dict.items())
                except:
                    display_data = "DBC decode error"
            else:
                display_data = "No DBC loaded"

        self.message_tree.item(item['tags'][0] if item['tags'] else '', values=(
            item['values'][0],
            item['values'][1],
            item['values'][2],
            display_data,
            item['values'][4]
        ))
        self.update_idletasks()

    def update_all_display_columns(self):
        for can_id, info in self.messages.items():
            item_id = info['item_id']
            item = self.message_tree.item(item_id)
            self.update_display_column(can_id, item)

    def open_interface_settings(self):
        settings_win = tk.Toplevel(self)
        settings_win.title("Interface Settings")
        settings_win.geometry("400x450")

        ttk.Label(settings_win, text="Adapter:").pack(pady=5)
        adapter_entry = ttk.Combobox(settings_win, values=self.available_adapters, state="readonly")
        adapter_entry.set(self.cfg['Interface'].get('bustype', 'slcan'))
        adapter_entry.pack(pady=5)

        ttk.Label(settings_win, text="Serial Port:").pack(pady=5)
        port_entry = ttk.Combobox(settings_win, values=self.get_serial_ports(), state="readonly")
        port_entry.set(self.cfg['Interface'].get('port', '/dev/ttyACM0'))
        port_entry.pack(pady=5)
        ttk.Button(settings_win, text="Refresh Ports", command=lambda: port_entry.config(values=self.get_serial_ports())).pack(pady=5)

        ttk.Label(settings_win, text="Channel:").pack(pady=5)
        channel_entry = ttk.Entry(settings_win)
        channel_entry.insert(0, self.cfg['Interface'].get('channel', 'can0'))
        channel_entry.pack(pady=5)

        ttk.Label(settings_win, text="CAN Bitrate (bps):").pack(pady=5)
        bitrate_entry = ttk.Combobox(settings_win, values=self.available_bitrates, state="readonly")
        bitrate_entry.set(self.cfg['Interface'].get('bitrate', '500000'))
        bitrate_entry.pack(pady=5)

        ttk.Label(settings_win, text="CAN FD Data Bitrate (bps):").pack(pady=5)
        data_bitrate_entry = ttk.Combobox(settings_win, values=self.available_data_bitrates, state="readonly")
        data_bitrate_entry.set(self.cfg['Interface'].get('data_bitrate', '2000000'))
        data_bitrate_entry.pack(pady=5)

        ttk.Label(settings_win, text="Serial Baud Rate:").pack(pady=5)
        baudrate_entry = ttk.Combobox(settings_win, values=self.available_baudrates, state="readonly")
        baudrate_entry.set(self.cfg['Interface'].get('baudrate', '115200'))
        baudrate_entry.pack(pady=5)

        ttk.Checkbutton(settings_win, text="Use 29-bit Extended IDs", variable=self.extended_id_var, command=self.update_send_labels).pack(pady=5)
        ttk.Checkbutton(settings_win, text="Enable CAN FD Mode", variable=self.can_fd_var, command=self.update_send_labels).pack(pady=5)

        ttk.Label(settings_win, text="Interface Response:").pack(pady=5)
        self.test_result = ttk.Label(settings_win, text="Not tested")
        self.test_result.pack(pady=5)
        ttk.Button(settings_win, text="Test Interface", command=lambda: self.test_interface(
            adapter_entry.get(), port_entry.get(), channel_entry.get(), bitrate_entry.get(),
            baudrate_entry.get(), data_bitrate_entry.get()
        )).pack(pady=5)

        def save_settings():
            self.cfg['Interface']['bustype'] = adapter_entry.get()
            self.cfg['Interface']['port'] = port_entry.get()
            self.cfg['Interface']['channel'] = channel_entry.get()
            self.cfg['Interface']['bitrate'] = bitrate_entry.get()
            self.cfg['Interface']['baudrate'] = baudrate_entry.get()
            self.cfg['Interface']['data_bitrate'] = data_bitrate_entry.get()
            self.cfg['Interface']['extended_id'] = str(self.extended_id_var.get())
            self.cfg['Interface']['can_fd'] = str(self.can_fd_var.get())
            self.save_config()
            self.serial_number = self.get_serial_number(port_entry.get(), int(baudrate_entry.get()))
            self.serial_label.config(text=f"Serial: {self.serial_number}")
            if self.bus:
                self.stop_can()
                self.start_can()
            settings_win.destroy()

        ttk.Button(settings_win, text="Save", command=save_settings).pack(pady=10)

    def test_interface(self, bustype, port, channel, bitrate, baudrate, data_bitrate):
        result = "Test failed"
        try:
            if bustype in self.serial_adapters:
                with serial.Serial(port, int(baudrate), timeout=1) as ser:
                    ser.write(b'V\r')
                    response = ser.read(10).decode('ascii', errors='ignore').strip()
                    if response:
                        result = f"Version: {response}"
                    else:
                        for p in serial.tools.list_ports.comports():
                            if p.device == port:
                                result = f"Port found: {p.description}"
                                break
                        else:
                            result = "Port accessible, no response"
                    self.serial_number = self.get_serial_number(port, int(baudrate))
                    self.serial_label.config(text=f"Serial: {self.serial_number}")
            else:
                bus_params = {
                    'interface': bustype,
                    'channel': channel,
                    'bitrate': int(bitrate),
                    'fd': self.can_fd_var.get(),
                    'data_bitrate': int(data_bitrate) if self.can_fd_var.get() else None
                }
                can.interface.Bus(**{k: v for k, v in bus_params.items() if v is not None})
                result = "Bus initialized successfully"
        except Exception as e:
            result = f"Error: {e}"
        self.test_result.config(text=result)

    def apply_filter(self, event):
        filter_text = self.filter_entry.get().strip()
        try:
            if filter_text:
                max_id = 0x1FFFFFFF if self.extended_id_var.get() else 0x7FF
                self.filter_ids = set(f"{int(id.strip(), 16):X}" for id in filter_text.split(',') if int(id.strip(), 16) <= max_id)
            else:
                self.filter_ids.clear()
            self.update_status_bar()
        except ValueError:
            messagebox.showerror("Error", "Invalid filter IDs (use hex, e.g., 123,456)")
            self.filter_entry.delete(0, tk.END)

    def toggle_pause(self):
        self.paused = not self.paused
        self.pause_btn.config(text="Resume" if self.paused else "Pause")
        self.update_status_bar()

    def reset_stats(self):
        self.id_stats.clear()
        self.message_count = 0
        self.message_rate = 0.0
        self.bus_load = 0.0
        for item in self.stats_tree.get_children():
            self.stats_tree.delete(item)
        self.update_stats()

    def toggle_dark_mode(self):
        style = ttk.Style()
        if self.dark_mode:
            style.theme_use('clam')
            style.configure('Treeview', background='#333333', foreground='white', fieldbackground='#333333')
            style.configure('TLabel', background='#222222', foreground='white')
            style.configure('TButton', background='#444444', foreground='white')
            style.configure('TFrame', background='#222222')
            self['bg'] = '#222222'
        else:
            style.theme_use('clam')
            style.configure('Treeview', background='#FFFFFF', foreground='black', fieldbackground='#FFFFFF')
            style.configure('TLabel', background='SystemButtonFace', foreground='black')
            style.configure('TButton', background='SystemButtonFace', foreground='black')
            style.configure('TFrame', background='SystemButtonFace')
            self['bg'] = 'SystemButtonFace'
        style.configure("Mono.Treeview", font=self.mono_font, rowheight=int(self.mono_font[1] * 2))
        self.update_highlight_tags()

    def load_dbc(self):
        if not cantools:
            messagebox.showerror("Error", "cantools not installed. Install with 'pip install cantools'")
            return
        dbc_file = filedialog.askopenfilename(filetypes=[("DBC Files", "*.dbc")])
        if dbc_file:
            try:
                self.dbc = cantools.db.load_file(dbc_file)
                messagebox.showinfo("Info", "DBC file loaded successfully")
                for can_id, info in self.messages.items():
                    if self.display_mode.get(can_id, 'binary') == 'decoded':
                        item_id = info['item_id']
                        item = self.message_tree.item(item_id)
                        self.update_display_column(can_id, item)
            except Exception as e:
                messagebox.showerror("Error", f"Failed to load DBC: {e}")

    def show_context_menu(self, event):
        item = self.message_tree.identify_row(event.y)
        if item:
            self.message_tree.selection_set(item)
            self.context_menu.post(event.x_root, event.y_root)

    def decode_selection(self, bit_length, endian='big'):
        selected = self.message_tree.selection()
        if not selected:
            return
        item = self.message_tree.item(selected[0])
        data = item['values'][2]
        try:
            data_bytes = bytes.fromhex(data.replace(' ', ''))
            if bit_length == 8:
                decoded = [f"{b:d}" for b in data_bytes]
            elif bit_length == 16:
                fmt = '>H' if endian == 'big' else '<H'
                decoded = [f"{struct.unpack_from(fmt, data_bytes, i)[0]:d}" for i in range(0, len(data_bytes), 2)]
            elif bit_length == 32:
                fmt = '>I' if endian == 'big' else '<I'
                decoded = [f"{struct.unpack_from(fmt, data_bytes, i)[0]:d}" for i in range(0, len(data_bytes), 4)]
            decoded_str = ', '.join(decoded)
            self.message_tree.item(selected[0], values=(
                item['values'][0],
                item['values'][1],
                item['values'][2],
                decoded_str,
                item['values'][4]
            ))
            self.update_idletasks()
        except Exception as e:
            messagebox.showerror("Error", f"Decoding failed: {e}")

    def clear_treeview(self):
        for item in self.message_tree.get_children():
            self.message_tree.delete(item)
        self.messages.clear()
        self.message_history.clear()
        self.last_data.clear()
        self.highlighted_rows.clear()
        self.display_mode.clear()
        self.last_message_timestamp = None
        self.update_idletasks()

    def update_status_bar(self):
        status = "Disconnected" if not self.bus else "Connected"
        if self.paused:
            status += " | Paused"
        if self.filter_ids:
            status += f" | Filtering: {','.join(self.filter_ids)}"
        mode = "CAN FD" if self.can_fd_var.get() else "CAN"
        id_type = "29-bit" if self.extended_id_var.get() else "11-bit"
        status += f" | Mode: {mode}, {id_type}"
        self.status_bar.config(text=status)
        self.update_info_labels()

    def update_info_labels(self):
        if self.bus:
            self.connection_indicator.itemconfig('indicator', fill='green')
            bustype = self.cfg['Interface']['bustype']
            channel = self.cfg['Interface']['port'] if bustype in self.serial_adapters else self.cfg['Interface']['channel']
            self.interface_label.config(text=f"Interface: {bustype} on {channel}")
            bitrate = self.cfg['Interface']['bitrate']
            data_bitrate = self.cfg['Interface'].get('data_bitrate', 'N/A') if self.can_fd_var.get() else 'N/A'
            self.stats_label.config(text=f"Baud: {bitrate} | Data: {data_bitrate} | Msg/s: {self.message_rate:.1f} | Bus Load: {self.bus_load:.1f}%")
        else:
            self.connection_indicator.itemconfig('indicator', fill='red')
            self.interface_label.config(text="Interface: Disconnected")
            self.stats_label.config(text="Baud: N/A | Data: N/A | Msg/s: 0.0 | Bus Load: 0.0%")
        self.serial_label.config(text=f"Serial: {self.serial_number}")

    def log_message(self, msg, direction, delta, timestamp):
        if not self.log_writer:
            return
        try:
            can_id = f"{msg.arbitration_id:X}"
            time_value = timestamp if self.time_mode == 'Timestamp' else f"{delta:06.3f}"
            data = ' '.join(f'{b:02X}' for b in msg.data)
            decoded = ""
            if self.dbc and cantools:
                try:
                    message = self.dbc.get_message_by_frame_id(msg.arbitration_id)
                    decoded_dict = message.decode(msg.data)
                    decoded = ', '.join(f"{k}: {v}" for k, v in decoded_dict.items())
                except:
                    decoded = "DBC decode error"
            self.log_writer.writerow([time_value, can_id, data, decoded, direction, msg.is_extended_id, msg.is_fd])
            self.log_file.flush()
        except Exception:
            pass

    def display_message(self, msg, direction="RX"):
        can_id = f"{msg.arbitration_id:X}"
        if self.paused or (direction == "RX" and self.filter_ids and can_id not in self.filter_ids):
            return

        self.message_count += 1
        delta = msg.timestamp - self.last_message_timestamp if self.last_message_timestamp else 0
        if delta < 0:
            delta = 0
        self.last_message_timestamp = msg.timestamp
        timestamp = datetime.fromtimestamp(msg.timestamp).strftime('%H:%M:%S.%f')[:-3]
        time_value = timestamp if self.time_mode == 'Timestamp' else f"{delta:06.3f}"
        data = ' '.join(f'{b:02X}' for b in msg.data)
        mode = self.display_mode.get(can_id, 'binary')
        endian = 'big' if self.endian_var.get() else 'little'

        if mode == 'binary':
            display_data = ' '.join(format(b, '08b').replace('0', '0').replace('1', '1') for b in msg.data)
        elif mode == 'dec8':
            display_data = ' '.join(f"{b:d}" for b in msg.data)
        elif mode == 'dec16':
            if len(msg.data) % 2 != 0:
                display_data = "N/A (Odd bytes)"
            else:
                values = []
                for i in range(0, len(msg.data), 2):
                    bytes_data = bytes([msg.data[i], msg.data[i+1]])
                    value = struct.unpack('>H' if endian == 'big' else '<H', bytes_data)[0]
                    values.append(str(value))
                display_data = ' '.join(values)
        else:
            if self.dbc and cantools:
                try:
                    message = self.dbc.get_message_by_frame_id(msg.arbitration_id)
                    decoded_dict = message.decode(msg.data)
                    display_data = ', '.join(f"{k}: {v}" for k, v in decoded_dict.items())
                except:
                    display_data = "DBC decode error"
            else:
                display_data = "No DBC loaded"

        if can_id not in self.id_stats:
            self.id_stats[can_id] = {'count': 0, 'first_timestamp': msg.timestamp, 'last_timestamp': msg.timestamp}
        self.id_stats[can_id]['count'] += 1
        self.id_stats[can_id]['last_timestamp'] = msg.timestamp
        if can_id not in self.message_history:
            self.message_history[can_id] = []
        self.message_history[can_id].append((msg.timestamp, msg.data))
        if len(self.message_history[can_id]) > 1000:
            self.message_history[can_id].pop(0)

        tags = self.messages.get(can_id, {}).get('tags', '') if can_id in self.messages else ''
        if direction == "RX" and self.highlight_changes_var.get():
            should_highlight = False
            if self.highlight_mode == 'Message':
                should_highlight = True
            elif self.highlight_mode == 'Message Change' and can_id in self.last_data and self.last_data[can_id] != data:
                should_highlight = True
            if should_highlight:
                tags = 'changed1'
                if can_id in self.highlighted_rows:
                    self.after_cancel(self.highlighted_rows[can_id].get('after_id', None))
                self.highlighted_rows[can_id] = {'level': 1}
                after_id = self.after(500, lambda: self.fade_highlight(can_id))
                self.highlighted_rows[can_id]['after_id'] = after_id

        if direction == "RX":
            self.last_data[can_id] = data

        if len(self.messages) >= self.max_messages:
            oldest_id = next(iter(self.messages))
            self.message_tree.delete(self.messages[oldest_id]['item_id'])
            del self.messages[oldest_id]
            if oldest_id in self.id_stats:
                del self.id_stats[oldest_id]
            if oldest_id in self.highlighted_rows:
                del self.highlighted_rows[oldest_id]

        if can_id in self.messages:
            item_id = self.messages[can_id]['item_id']
            self.message_tree.item(item_id, values=(time_value, can_id, data, display_data, direction), tags=tags)
            self.messages[can_id].update({
                'item_id': item_id,
                'timestamp': msg.timestamp,
                'timestamp_str': timestamp,
                'delta': delta,
                'tags': tags
            })
        else:
            item_id = self.message_tree.insert("", "end", values=(time_value, can_id, data, display_data, direction), tags=tags)
            self.messages[can_id] = {
                'item_id': item_id,
                'timestamp': msg.timestamp,
                'timestamp_str': timestamp,
                'delta': delta,
                'tags': tags
            }
        self.message_tree.see(item_id)
        self.update_idletasks()
        self.log_message(msg, direction, delta, timestamp)
        self.update_stats()

    def fade_highlight(self, can_id):
        if can_id not in self.messages or can_id not in self.highlighted_rows:
            return
        item_id = self.messages[can_id]['item_id']
        highlight_info = self.highlighted_rows[can_id]
        level = highlight_info['level']
        values = self.message_tree.item(item_id)['values']
        if level <= 7:
            tags = f'changed{level + 1}'
            highlight_info['level'] = level + 1
            after_id = self.after(500, lambda: self.fade_highlight(can_id))
            highlight_info['after_id'] = after_id
        else:
            tags = ''
            del self.highlighted_rows[can_id]
        self.message_tree.item(item_id, values=values, tags=tags)
        self.messages[can_id]['tags'] = tags
        self.update_idletasks()

    def start_can(self):
        if self.bus:
            return
        try:
            interface = self.cfg['Interface']
            bustype = interface['bustype']
            channel = interface['port'] if bustype in self.serial_adapters else interface.get('channel', 'can0')
            bitrate = int(interface['bitrate'])
            data_bitrate = int(interface.get('data_bitrate', '2000000')) if self.can_fd_var.get() else None
            bus_params = {
                'interface': bustype,
                'channel': channel,
                'bitrate': bitrate,
                'fd': self.can_fd_var.get(),
                'data_bitrate': data_bitrate
            }
            if bustype in self.serial_adapters:
                baudrate = int(interface.get('baudrate', '115200'))
                bus_params['serial_port_baudrate'] = baudrate
                self.serial_number = self.get_serial_number(channel, baudrate)
                self.serial_label.config(text=f"Serial: {self.serial_number}")
            self.bus = can.interface.Bus(**{k: v for k, v in bus_params.items() if v is not None})
            self.running = True
            self.last_message_timestamp = None
            self.message_count = 0
            self.message_rate = 0.0
            self.bus_load = 0.0
            self.can_error_count = 0
            self.update_status_bar()
            self.receiver_thread = threading.Thread(target=self.receive_loop, daemon=True)
            self.receiver_thread.start()
        except Exception as e:
            self.status_bar.config(text=f"Disconnected: {e}")
            self.connection_indicator.itemconfig('indicator', fill='red')
            messagebox.showerror("Error", f"Failed to start CAN: {e}")

    def stop_can(self):
        self.running = False
        self.stop_periodic()
        while not self.message_queue.empty():
            try:
                self.message_queue.get_nowait()
            except queue.Empty:
                break
        if hasattr(self, 'receiver_thread') and self.receiver_thread.is_alive():
            self.receiver_thread.join(timeout=2.0)
        if self.bus:
            try:
                self.bus.shutdown()
            except Exception:
                pass
            finally:
                self.bus = None
        self.last_message_timestamp = None
        self.message_count = 0
        self.message_rate = 0.0
        self.bus_load = 0.0
        self.can_error_count = 0
        self.update_status_bar()

    def receive_loop(self):
        while self.running:
            try:
                msg = self.bus.recv(timeout=0.1)
                if msg:
                    self.message_queue.put(msg)
                    self.can_error_count = 0
                else:
                    pass
            except can.CanError as e:
                self.can_error_count += 1
                if self.can_error_count > 10:
                    self.message_queue.put(Exception(f"Excessive CAN errors: {e}"))
                    break
                if self.running:
                    continue
                else:
                    break
            except Exception as e:
                if self.running:
                    self.message_queue.put(e)
                    break

    def check_queue(self):
        try:
            batch_size = 5
            processed = 0
            while processed < batch_size:
                item = self.message_queue.get_nowait()
                processed += 1
                if isinstance(item, Exception):
                    if self.running:
                        messagebox.showerror("Error", f"Receive error: {item}")
                        self.stop_can()
                    break
                if not self.paused:
                    self.display_message(item, direction="RX")
        except queue.Empty:
            pass
        except Exception:
            pass
        self.after(50, self.check_queue)

    def schedule_stats_update(self):
        self.update_stats()
        self.after(1000, self.schedule_stats_update)

    def update_stats(self):
        current_time = time.time()
        elapsed = current_time - self.last_stats_update
        if elapsed > 0:
            self.message_rate = self.message_count / elapsed
            bitrate = int(self.cfg['Interface'].get('bitrate', 500000))
            bits_per_message = (128 + 64) if self.can_fd_var.get() else (47 + 64)
            self.bus_load = (self.message_rate * bits_per_message / bitrate) * 100
            if self.bus_load > 100:
                self.bus_load = 100
            self.message_count = 0
            self.last_stats_update = current_time
        self.update_info_labels()

        for item in self.stats_tree.get_children():
            self.stats_tree.delete(item)
        for can_id, stats in self.id_stats.items():
            count = stats['count']
            last_time = datetime.fromtimestamp(stats['last_timestamp']).strftime('%H:%M:%S.%f')[:-3]
            if count >= 2 and 'first_timestamp' in stats:
                duration = stats['last_timestamp'] - stats['first_timestamp']
                frequency = count / duration if duration > 0 else 0
            else:
                frequency = 0
            self.stats_tree.insert("", "end", values=(can_id, count, last_time, f"{frequency:.2f}"))
        self.update_idletasks()

    def send_once(self):
        if not self.bus:
            messagebox.showerror("Error", "CAN bus not connected")
            return
        inputs = self.validate_send_inputs()
        if inputs is None:
            return
        can_id, data, _ = inputs
        try:
            msg = can.Message(
                arbitration_id=can_id,
                data=data,
                is_extended_id=self.extended_id_var.get(),
                is_fd=self.can_fd_var.get(),
                bitrate_switch=self.can_fd_var.get()
            )
            msg.timestamp = time.time()
            self.bus.send(msg)
            self.display_message(msg, direction="TX")
            messagebox.showinfo("Success", f"Message sent: ID={hex(can_id)}, Data={' '.join(f'{b:02X}' for b in data)}")
        except can.CanError as e:
            messagebox.showerror("Error", f"CAN error sending message: {e}")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to send: {e}")

    def toggle_periodic(self):
        if not self.bus:
            messagebox.showerror("Error", "CAN bus not connected")
            self.send_periodic_var.set(False)
            self.send_periodic_check.update()
            self.update_idletasks()
            return

        if self.send_periodic_var.get():
            inputs = self.validate_send_inputs()
            if inputs is None:
                self.stop_periodic()
                return
            can_id, data, interval = inputs
            try:
                if interval < 10:
                    raise ValueError("Interval must be at least 10ms")
                self.schedule_periodic_send(can_id, data, interval)
                self.send_periodic_check.update()
                self.update_idletasks()
            except ValueError as e:
                messagebox.showerror("Error", f"Invalid interval: {e}")
                self.stop_periodic()
            except Exception as e:
                messagebox.showerror("Error", f"Failed to start periodic send: {e}")
                self.stop_periodic()
        else:
            self.stop_periodic()

    def schedule_periodic_send(self, can_id, data, interval):
        if not self.send_periodic_var.get() or not self.bus:
            self.stop_periodic()
            return
        try:
            msg = can.Message(
                arbitration_id=can_id,
                data=data,
                is_extended_id=self.extended_id_var.get(),
                is_fd=self.can_fd_var.get(),
                bitrate_switch=self.can_fd_var.get()
            )
            msg.timestamp = time.time()
            self.bus.send(msg)
            self.display_message(msg, direction="TX")
        except can.CanError as e:
            messagebox.showerror("Error", f"CAN error sending periodic message: {e}")
            self.stop_periodic()
            return
        except Exception as e:
            messagebox.showerror("Error", f"Failed to send periodic message: {e}")
            self.stop_periodic()
            return
        self.periodic_task_id = self.after(int(interval), lambda: self.schedule_periodic_send(can_id, data, interval))

    def stop_periodic(self):
        if self.periodic_task_id is not None:
            self.after_cancel(self.periodic_task_id)
            self.periodic_task_id = None
        if self.send_periodic_var.get():
            self.send_periodic_var.set(False)
        self.send_periodic_check.update()
        self.update_idletasks()

    def resend_selected(self):
        if not self.bus:
            messagebox.showerror("Error", "CAN bus not connected")
            return
        selected = self.message_tree.selection()
        if not selected:
            messagebox.showerror("Error", "Select a message to resend")
            return
        item = self.message_tree.item(selected[0])
        can_id = int(item['values'][1], 16)
        data_str = item['values'][2]
        try:
            data = bytes.fromhex(data_str.replace(' ', ''))
            max_bytes = 64 if self.can_fd_var.get() else 8
            if len(data) > max_bytes:
                messagebox.showerror("Error", f"Data length exceeds {max_bytes} bytes for current mode")
                return
            max_id = 0x1FFFFFFF if self.extended_id_var.get() else 0x7FF
            if can_id > max_id:
                messagebox.showerror("Error", f"CAN ID {hex(can_id)} exceeds {hex(max_id)} for current mode")
                return
            msg = can.Message(
                arbitration_id=can_id,
                data=data,
                is_extended_id=self.extended_id_var.get(),
                is_fd=self.can_fd_var.get(),
                bitrate_switch=self.can_fd_var.get()
            )
            msg.timestamp = time.time()
            self.bus.send(msg)
            self.display_message(msg, direction="TX")
            messagebox.showinfo("Success", f"Message resent: ID={hex(can_id)}, Data={' '.join(f'{b:02X}' for b in data)}")
        except can.CanError as e:
            messagebox.showerror("Error", f"CAN error resending message: {e}")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to resend: {e}")

    def start_logging(self):
        if self.log_file:
            messagebox.showinfo("Info", "Logging already active")
            return
        log_file = self.cfg['Logging']['log_file']
        try:
            self.log_file = open(log_file, 'w', newline='')
            self.log_writer = csv.writer(self.log_file)
            self.log_writer.writerow(["Time", "ID", "Data", "Display", "Direction", "Extended", "FD"])
            messagebox.showinfo("Info", f"Logging started to {log_file}")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to start logging: {e}")

    def stop_logging(self):
        if self.log_file:
            try:
                self.log_file.close()
            except Exception:
                pass
            finally:
                self.log_file = None
                self.log_writer = None
            messagebox.showinfo("Info", "Logging stopped")

    def copy_selection(self, event=None):
        selected = self.message_tree.selection()
        if not selected:
            return
        lines = []
        for item in selected:
            values = self.message_tree.item(item)['values']
            lines.append('\t'.join(str(v) for v in values))
        self.clipboard_clear()
        self.clipboard_append('\n'.join(lines))
        messagebox.showinfo("Info", "Selection copied to clipboard")

    def diff_selected(self):
        selected = self.message_tree.selection()
        if len(selected) != 2:
            messagebox.showerror("Error", "Select exactly two messages")
            return
        item1 = self.message_tree.item(selected[0])
        item2 = self.message_tree.item(selected[1])
        data1 = item1['values'][2].split()
        data2 = item2['values'][2].split()
        if len(data1) != len(data2):
            messagebox.showinfo("Diff", "Messages have different data lengths")
            return
        diff = []
        for i, (b1, b2) in enumerate(zip(data1, data2)):
            if b1 != b2:
                diff.append(f"Byte {i}: {b1} != {b2}")
        message = "\n".join(diff) if diff else "No differences"
        messagebox.showinfo("Diff", message)

    def plot_signals(self):
        if not cantools or not self.dbc:
            messagebox.showerror("Error", "DBC not loaded or cantools not installed")
            return
        if not plt or not Figure:
            messagebox.showerror("Error", "matplotlib not installed. Install with 'pip install matplotlib'")
            return
        selected = self.message_tree.selection()
        if not selected:
            messagebox.showerror("Error", "Select a message to plot")
            return
        can_id = self.message_tree.item(selected[0])['values'][1]
        try:
            message = self.dbc.get_message_by_frame_id(int(can_id, 16))
            signals = message.signals
            if not signals:
                messagebox.showinfo("Info", "No signals in this message")
                return
            signal_names = [s.name for s in signals]
            selected_signals = []
            time_window = tk.StringVar(value="60")

            def on_select():
                nonlocal selected_signals
                selected_signals = [signal_names[i] for i in listbox.curselection()]

            def plot():
                try:
                    window = float(time_window.get())
                    if window <= 0:
                        raise ValueError("Time window must be positive")
                    top.destroy()
                    do_plot_signals(selected_signals, window)
                except ValueError as e:
                    messagebox.showerror("Error", f"Invalid time window: {e}")

            def do_plot_signals(selected_signals, window):
                if not selected_signals:
                    return
                fig = Figure()
                ax = fig.add_subplot(111)
                lines = []
                for signal_name in selected_signals:
                    line, = ax.plot([], [], label=signal_name)
                    lines.append((signal_name, line))
                ax.set_xlabel("Time (s, relative to latest)")
                ax.set_ylabel("Signal Value")
                ax.set_xlim(-window, 0)
                ax.legend()
                ax.set_title(f"Signals for CAN ID {can_id}")

                plot_window = tk.Toplevel(self)
                plot_window.title(f"Signal Plot for CAN ID {can_id}")
                canvas = FigureCanvasTkAgg(fig, master=plot_window)
                canvas.get_tk_widget().pack(fill="both", expand=True)
                canvas.draw()

                plot_open = True

                def on_plot_close():
                    nonlocal plot_open
                    plot_open = False
                    plot_window.destroy()

                plot_window.protocol("WM_DELETE_WINDOW", on_plot_close)

                def update_plot():
                    if not plot_open:
                        return
                    try:
                        if can_id not in self.message_history:
                            return
                        latest_time = max((t for t, _ in self.message_history[can_id]), default=time.time())
                        for signal_name, line in lines:
                            signal = next(s for s in signals if s.name == signal_name)
                            values = []
                            times = []
                            for timestamp, data in self.message_history[can_id]:
                                if latest_time - timestamp <= window:
                                    try:
                                        decoded = message.decode(data)
                                        value = decoded[signal_name]
                                        values.append(value)
                                        times.append(timestamp - latest_time)
                                    except:
                                        continue
                            if values:
                                line.set_data(times, values)
                        ax.relim()
                        ax.autoscale_view(scaley=True)
                        canvas.draw()
                        plot_window.after(1000, update_plot)
                    except Exception:
                        pass

                update_plot()

            top = tk.Toplevel(self)
            top.title("Select Signals")
            ttk.Label(top, text="Time Window (s):").pack(pady=5)
            time_entry = ttk.Entry(top, textvariable=time_window, width=10)
            time_entry.pack(pady=5)
            listbox = tk.Listbox(top, selectmode="multiple")
            for signal in signal_names:
                listbox.insert(tk.END, signal)
            listbox.pack(padx=5, pady=5)
            ttk.Button(top, text="Plot", command=lambda: [on_select(), plot()]).pack(pady=5)
            top.wait_window()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to plot: {e}")

    def analyze_bytes(self):
        selected = self.message_tree.selection()
        if not selected:
            messagebox.showerror("Error", "Select a message to analyze")
            return
        can_id = self.message_tree.item(selected[0])['values'][1]
        if can_id not in self.message_history or not self.message_history[can_id]:
            messagebox.showinfo("Info", "No history for this ID")
            return
        analysis_win = tk.Toplevel(self)
        analysis_win.title(f"Byte Analysis for ID {can_id}")
        analysis_win['bg'] = '#222222' if self.dark_mode else 'SystemButtonFace'
        time_window = tk.StringVar(value="60")

        ttk.Label(analysis_win, text="Time Window (s):").pack(pady=5)
        time_entry = ttk.Entry(analysis_win, textvariable=time_window, width=10)
        time_entry.pack(pady=5)

        byte_labels = {}
        max_bytes = 64 if self.can_fd_var.get() else 8
        for i in range(max_bytes):
            label = ttk.Label(analysis_win, text=f"Byte {i}: No data")
            label.pack(pady=2)
            byte_labels[i] = label
            if plt:
                def plot_byte_wrapper(byte_index=i):
                    try:
                        window = float(time_window.get())
                        if window <= 0:
                            raise ValueError("Time window must be positive")
                        plot_byte(byte_index, window)
                    except ValueError as e:
                        messagebox.showerror("Error", f"Invalid time window: {e}")

                ttk.Button(analysis_win, text=f"Plot Byte {i}", command=plot_byte_wrapper).pack(pady=2)

        def plot_byte(byte_index, window):
            try:
                fig = Figure()
                ax = fig.add_subplot(111)
                line, = ax.plot([], [], label=f"Byte {byte_index}")
                ax.set_xlabel("Time (s, relative to latest)")
                ax.set_ylabel("Value")
                ax.set_xlim(-window, 0)
                ax.legend()
                ax.set_title(f"Byte {byte_index} for CAN ID {can_id}")

                plot_window = tk.Toplevel(self)
                plot_window.title(f"Byte {byte_index} Plot for CAN ID {can_id}")
                canvas = FigureCanvasTkAgg(fig, master=plot_window)
                canvas.get_tk_widget().pack(fill="both", expand=True)
                canvas.draw()

                plot_open = True

                def on_plot_close():
                    nonlocal plot_open
                    plot_open = False
                    plot_window.destroy()

                plot_window.protocol("WM_DELETE_WINDOW", on_plot_close)

                def update_byte_plot():
                    if not plot_open:
                        return
                    try:
                        latest_time = max((t for t, _ in self.message_history[can_id]), default=time.time())
                        times = []
                        values = []
                        for timestamp, data in self.message_history[can_id]:
                            if byte_index < len(data) and latest_time - timestamp <= window:
                                times.append(timestamp - latest_time)
                                values.append(data[byte_index])
                        if values:
                            line.set_data(times, values)
                            ax.relim()
                            ax.autoscale_view(scaley=True)
                            canvas.draw()
                        plot_window.after(1000, update_byte_plot)
                    except Exception:
                        pass

                update_byte_plot()
            except Exception as e:
                messagebox.showerror("Error", f"Failed to plot byte {byte_index}: {e}")

        analysis_open = True

        def on_analysis_close():
            nonlocal analysis_open
            analysis_open = False
            analysis_win.destroy()

        analysis_win.protocol("WM_DELETE_WINDOW", on_analysis_close)

        def update_analysis():
            if not analysis_open:
                return
            try:
                window = float(time_window.get())
                if window <= 0:
                    return
                latest_time = max((t for t, _ in self.message_history[can_id]), default=time.time())
                for i in range(max_bytes):
                    values = []
                    for timestamp, data in self.message_history[can_id]:
                        if i < len(data) and latest_time - timestamp <= window:
                            values.append(data[i])
                    if values:
                        min_val = min(values)
                        max_val = max(values)
                        mean_val = sum(values) / len(values)
                        byte_labels[i].config(text=f"Byte {i}: Min={min_val}, Max={max_val}, Mean={mean_val:.2f}")
                    else:
                        byte_labels[i].config(text=f"Byte {i}: No data")
                analysis_win.after(1000, update_analysis)
            except Exception:
                pass

        update_analysis()

    def on_closing(self):
        self.stop_can()
        self.stop_logging()
        self.running = False
        self.destroy()

if __name__ == "__main__":
    app = CANApp()
    app.mainloop()
