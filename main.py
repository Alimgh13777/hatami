import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog
import asyncio
import random
import threading
import queue
import csv
import re
import time
from datetime import datetime
from collections import deque

from telethon import TelegramClient
from telethon.errors import (
    FloodWaitError, SessionPasswordNeededError, PhoneCodeInvalidError,
    PhoneCodeExpiredError, PhoneCodeEmptyError, PeerFloodError,
    UserPrivacyRestrictedError, ChatWriteForbiddenError,
    UsernameNotOccupiedError, UserIdInvalidError, PhoneNumberBannedError,
    MessageDeleteForbiddenError, ChatAdminRequiredError
)
from telethon.tl.functions.contacts import ImportContactsRequest
from telethon.tl.types import InputPhoneContact

# -------------------------------------------------------------------
# LoginHelper with thread‑safe cancel
# -------------------------------------------------------------------
class LoginHelper:
    def __init__(self, app):
        self.app = app
        self.queue = queue.Queue()
        self.pending_futures = set()

    async def request_phone(self, prompt="Enter phone number:"):
        return await self._request('phone', prompt)

    async def request_code(self, prompt="Enter verification code:"):
        return await self._request('code', prompt)

    async def request_password(self, prompt="Enter 2FA password:", show="*"):
        return await self._request('password', prompt, show=show)

    async def _request(self, field_type, prompt, show=None):
        loop = asyncio.get_running_loop()
        future = loop.create_future()
        self.pending_futures.add(future)
        self.queue.put((field_type, prompt, show, future))
        try:
            return await future
        finally:
            self.pending_futures.discard(future)

    def cancel_all(self):
        loop = self.app.loop
        if loop is None or loop.is_closed():
            self.pending_futures.clear()
            return
        if loop.is_running():
            while not self.queue.empty():
                try:
                    _, _, _, future = self.queue.get_nowait()
                    if not future.done():
                        loop.call_soon_threadsafe(future.set_result, None)
                    self.pending_futures.discard(future)
                except queue.Empty:
                    break
            for future in list(self.pending_futures):
                if not future.done():
                    loop.call_soon_threadsafe(future.set_result, None)
                self.pending_futures.discard(future)
        else:
            self.pending_futures.clear()

# -------------------------------------------------------------------
# Main Application
# -------------------------------------------------------------------
class TelegramSenderApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Telegram Bulk Sender – Limit Tester Pro (Final)")
        self.root.geometry("1050x850")
        self.root.minsize(950, 780)

        # Style
        self.style = ttk.Style()
        self.style.theme_use("clam")
        self.style.configure("TLabel", font=("Segoe UI", 9))
        self.style.configure("TButton", font=("Segoe UI", 9, "bold"))
        self.style.configure("Header.TLabel", font=("Segoe UI", 10, "bold"))
        self.style.configure("Status.TLabel", font=("Segoe UI", 9), foreground="#2c3e50")

        # Variables
        self.api_id = tk.StringVar(value="")
        self.api_hash = tk.StringVar(value="")
        self.input_mode = tk.StringVar(value="phone")
        self.min_delay = tk.StringVar(value="2")
        self.max_delay = tk.StringVar(value="5")
        self.batch_size = tk.StringVar(value="5")
        self.batch_interval = tk.StringVar(value="120")
        self.retry_count = tk.StringVar(value="2")

        self.targets = deque()
        self.accounts = []
        self.loop = None
        self.main_task = None
        self._send_tasks = set()       # track send tasks for cancellation
        self.is_sending = False
        self.stop_flag = threading.Event()
        self.login_helper = LoginHelper(self)
        self.stats_lock = threading.Lock()
        self._cached_msg = None

        # Validators
        self.phone_re = re.compile(r'^\+\d{7,15}$')
        self.username_re = re.compile(r'^@?[a-zA-Z][a-zA-Z0-9_]{4,31}$')
        self.id_re = re.compile(r'^\d{5,}$')

        self.create_widgets()
        self._start_login_queue_checker()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    # -------------------------------------------------------------------
    # UI
    # -------------------------------------------------------------------
    def create_widgets(self):
        main = ttk.Frame(self.root, padding="10")
        main.pack(fill="both", expand=True)

        # --- API Credentials ---
        cred = ttk.LabelFrame(main, text="API Credentials (my.telegram.org)", padding="10")
        cred.pack(fill="x", pady=(0, 10))
        cred_frame = ttk.Frame(cred)
        cred_frame.pack(fill="x")
        ttk.Label(cred_frame, text="API ID:").pack(side="left", padx=(0, 3))
        api_id_entry = ttk.Entry(cred_frame, textvariable=self.api_id, width=12)
        api_id_entry.pack(side="left", padx=(0, 15))
        ttk.Label(cred_frame, text="API Hash:").pack(side="left", padx=(0, 3))
        api_hash_entry = ttk.Entry(cred_frame, textvariable=self.api_hash, width=30, show="*")
        api_hash_entry.pack(side="left")
        self._add_context_menu(api_id_entry)
        self._add_context_menu(api_hash_entry)

        # --- Accounts ---
        acc_frame = ttk.LabelFrame(main, text="Accounts (phones)", padding="10")
        acc_frame.pack(fill="x", pady=(0,10))
        listf = ttk.Frame(acc_frame)
        listf.pack(side="left", fill="both", expand=True)
        self.acc_listbox = tk.Listbox(listf, height=5, selectmode="extended", exportselection=False)
        scroll = ttk.Scrollbar(listf, orient="vertical", command=self.acc_listbox.yview)
        self.acc_listbox.configure(yscrollcommand=scroll.set)
        self.acc_listbox.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")
        btnf = ttk.Frame(acc_frame)
        btnf.pack(side="right", fill="y", padx=(5,0))
        ttk.Button(btnf, text="Add", command=self.add_account).pack(pady=2, fill="x")
        ttk.Button(btnf, text="Remove", command=self.remove_account).pack(pady=2, fill="x")
        ttk.Button(btnf, text="Load from file", command=self.load_accounts).pack(pady=2, fill="x")

        # --- Target Type ---
        modef = ttk.LabelFrame(main, text="Target Type", padding="10")
        modef.pack(fill="x", pady=(0,10))
        for text, val in [("Phone Numbers", "phone"), ("User IDs", "id"), ("Usernames", "username")]:
            ttk.Radiobutton(modef, text=text, variable=self.input_mode, value=val).pack(side="left", padx=10)

        # --- Target List ---
        tgt_frame = ttk.LabelFrame(main, text="Target List", padding="10")
        tgt_frame.pack(fill="both", expand=True, pady=(0,10))
        self.num_text = tk.Text(tgt_frame, height=7, width=80, wrap="none", font=("Consolas",9))
        self.num_text.pack(side="left", fill="both", expand=True)
        self._add_context_menu(self.num_text)
        btn_t = ttk.Frame(tgt_frame)
        btn_t.pack(side="right", fill="y", padx=(5,0))
        ttk.Button(btn_t, text="Load Excel", command=self.load_excel).pack(pady=3, fill="x")
        ttk.Button(btn_t, text="Clear", command=self.clear_targets).pack(pady=3, fill="x")

        # --- Message & Timing ---
        msg_frame = ttk.LabelFrame(main, text="Message & Timing", padding="10")
        msg_frame.pack(fill="x", pady=(0,10))

        ttk.Label(msg_frame, text="Message (use {emoji}, {counter}):").pack(anchor="w")
        self.msg_text = tk.Text(msg_frame, height=3, width=80, wrap="word", font=("Tahoma",9))
        self.msg_text.pack(fill="x", pady=(0,10))
        self._add_context_menu(self.msg_text)

        timing_frame = ttk.Frame(msg_frame)
        timing_frame.pack(fill="x")

        ttk.Label(timing_frame, text="Batch Size:").grid(row=0, column=0, sticky="e", padx=(0,3), pady=3)
        batch_size_entry = ttk.Entry(timing_frame, textvariable=self.batch_size, width=5)
        batch_size_entry.grid(row=0, column=1, padx=(0,10), pady=3)

        ttk.Label(timing_frame, text="Interval (s):").grid(row=0, column=2, sticky="e", padx=(0,3), pady=3)
        batch_int_entry = ttk.Entry(timing_frame, textvariable=self.batch_interval, width=5)
        batch_int_entry.grid(row=0, column=3, padx=(0,10), pady=3)

        ttk.Label(timing_frame, text="Min delay (s):").grid(row=0, column=4, sticky="e", padx=(0,3), pady=3)
        min_delay_entry = ttk.Entry(timing_frame, textvariable=self.min_delay, width=5)
        min_delay_entry.grid(row=0, column=5, padx=(0,10), pady=3)

        ttk.Label(timing_frame, text="Max delay (s):").grid(row=0, column=6, sticky="e", padx=(0,3), pady=3)
        max_delay_entry = ttk.Entry(timing_frame, textvariable=self.max_delay, width=5)
        max_delay_entry.grid(row=0, column=7, pady=3)

        ttk.Label(timing_frame, text="Retries:").grid(row=1, column=0, sticky="e", padx=(0,3), pady=3)
        retry_count_entry = ttk.Entry(timing_frame, textvariable=self.retry_count, width=5)
        retry_count_entry.grid(row=1, column=1, pady=3, sticky="w")

        for ent in (batch_size_entry, batch_int_entry, min_delay_entry, max_delay_entry, retry_count_entry):
            self._add_context_menu(ent)

        # --- Control buttons ---
        ctrl = ttk.Frame(main)
        ctrl.pack(fill="x", pady=(0,10))
        self.start_btn = ttk.Button(ctrl, text="▶ Start", command=self.start_sending)
        self.start_btn.pack(side="left", padx=5)
        self.stop_btn = ttk.Button(ctrl, text="⏹ Stop", command=self.stop_sending, state="disabled")
        self.stop_btn.pack(side="left", padx=5)
        self.export_btn = ttk.Button(ctrl, text="📊 Export CSV", command=self.export_csv, state="disabled")
        self.export_btn.pack(side="left", padx=5)
        self.progress = ttk.Progressbar(ctrl, mode="determinate", length=200)
        self.progress.pack(side="right", padx=10)

        # --- Status bar ---
        self.status_var = tk.StringVar(value="Ready")
        ttk.Label(main, textvariable=self.status_var, style="Status.TLabel",
                  relief="sunken", anchor="w", padding=(5,2)).pack(fill="x", pady=(0,5))

        # --- Log ---
        logf = ttk.LabelFrame(main, text="Log", padding="5")
        logf.pack(fill="both", expand=True)
        self.log = scrolledtext.ScrolledText(logf, height=10, state="disabled", wrap="word",
                                             font=("Consolas",9))
        self.log.pack(fill="both", expand=True)
        self.log.tag_config("info", foreground="#2c3e50")
        self.log.tag_config("success", foreground="#27ae60")
        self.log.tag_config("warn", foreground="#f39c12")
        self.log.tag_config("error", foreground="#e74c3c")
        self.log.tag_config("spam", foreground="#8e44ad")
        self.log.tag_config("title", foreground="#2c3e50", font=("Consolas",9,"bold"))

        self.stats_win = None

    # -------------------------------------------------------------------
    # Right-click context menu
    # -------------------------------------------------------------------
    def _add_context_menu(self, widget):
        menu = tk.Menu(widget, tearoff=0)
        menu.add_command(label="Cut", command=lambda: widget.event_generate("<<Cut>>"))
        menu.add_command(label="Copy", command=lambda: widget.event_generate("<<Copy>>"))
        menu.add_command(label="Paste", command=lambda: widget.event_generate("<<Paste>>"))
        menu.add_separator()
        menu.add_command(label="Select All", command=lambda: self._select_all(widget))

        def show_menu(event):
            menu.tk_popup(event.x_root, event.y_root)
        widget.bind("<Button-3>", show_menu)
        widget.bind("<Button-2>", show_menu)

    def _select_all(self, widget):
        try:
            widget.select_range(0, "end")
        except AttributeError:
            try:
                widget.selection_range(0, "end")
            except:
                pass

    # -------------------------------------------------------------------
    # Helpers
    # -------------------------------------------------------------------
    def _get_positive_int(self, var, name, min_val=1):
        try:
            val = int(var.get())
            if val < min_val:
                raise ValueError
            return val
        except (ValueError, tk.TclError):
            messagebox.showerror("Invalid", f"{name} must be an integer ≥ {min_val}.")
            return None

    def _normalize_phone(self, s):
        s = s.strip()
        if not s.startswith("+"):
            if s.startswith("00"):
                s = "+" + s[2:]
            elif s.startswith("0") and len(s) == 11:
                s = "+98" + s[1:]
            elif s.isdigit() and len(s) == 10 and s.startswith("9"):
                s = "+98" + s
            elif s.isdigit():
                s = "+" + s
        return s

    @staticmethod
    def mask_phone(phone):
        if len(phone) < 8: return phone
        return phone[:5] + "***" + phone[-4:]

    # -------------------------------------------------------------------
    # Account management (using safe custom dialogs)
    # -------------------------------------------------------------------
    def add_account(self):
        phone = self._ask_string("Add Account", "Phone number (+98...):")
        if not phone or not self.phone_re.match(phone.strip()):
            messagebox.showwarning("Invalid", "Enter valid phone (+98...).")
            return
        phone = phone.strip()
        if any(acc["phone"] == phone for acc in self.accounts):
            messagebox.showwarning("Duplicate", "This number already exists.")
            return
        clean = phone.replace("+","").replace(" ","")
        session = f"{clean}_{int(time.time()*1e6)}_{random.randint(0,999)}"
        self.acc_listbox.insert("end", f"{phone} [session: {session}]")
        self.accounts.append(self._new_account_dict(phone, session))

    def _new_account_dict(self, phone, session):
        return {
            "phone": phone,
            "session": session,
            "client": None,
            "authorized": False,
            "sent_hour": 0,
            "spam_count": 0,
            "blocked": False,
            "hourly_log": [],
            "last_hour": datetime.now().hour,
            "target_contact_count": 0,
            "target_total": 0,
            "contact_ratio": 0.0
        }

    def remove_account(self):
        sel = self.acc_listbox.curselection()
        for idx in reversed(sel):
            self.acc_listbox.delete(idx)
            del self.accounts[idx]

    def load_accounts(self):
        path = filedialog.askopenfilename(filetypes=[("Text files","*.txt")])
        if not path: return
        with open(path, "r", encoding="utf-8") as f:
            phones = [line.strip() for line in f if line.strip()]
        valid_phones = []
        for phone in phones:
            if not self.phone_re.match(phone):
                self.log_message(f"⚠ Skipped invalid phone: {phone}", "warn")
                continue
            if any(acc["phone"] == phone for acc in self.accounts):
                self.log_message(f"⚠ Duplicate skipped: {phone}", "warn")
                continue
            clean = phone.replace("+","").replace(" ","")
            session = f"{clean}_{int(time.time()*1e6)}_{random.randint(0,999)}"
            self.acc_listbox.insert("end", f"{phone} [session: {session}]")
            self.accounts.append(self._new_account_dict(phone, session))
            valid_phones.append(phone)
        self.log_message(f"✔ Loaded {len(valid_phones)} valid accounts.")

    # -------------------------------------------------------------------
    # Log / Status
    # -------------------------------------------------------------------
    def log_message(self, msg, tag="info"):
        try:
            if not self.root.winfo_exists():
                return
            self.log.configure(state="normal")
            self.log.insert("end", msg + "\n", tag)
            lines = int(self.log.index('end-1c').split('.')[0])
            if lines > 1000:
                self.log.delete("1.0", f"{lines-1000}.0")
            self.log.see("end")
            self.log.configure(state="disabled")
        except tk.TclError:
            pass

    def set_status(self, text):
        try:
            if self.root.winfo_exists():
                self.status_var.set(text)
        except tk.TclError:
            pass

    def log_ui(self, msg, tag="info"):
        self.root.after(0, self.log_message, msg, tag)

    def status_ui(self, text):
        self.root.after(0, self.set_status, text)

    # -------------------------------------------------------------------
    # Custom async exception handler (prevents cryptic logs)
    # -------------------------------------------------------------------
    def _handle_async_exception(self, loop, context):
        exc = context.get('exception')
        if exc and isinstance(exc, asyncio.CancelledError):
            # CancelledError is normal after stop, ignore
            return
        msg = context.get('message', 'Async exception')
        if exc:
            # Cleanly log the exception type and its message, no chained causes
            msg = f"{msg}: {type(exc).__name__}: {exc}"
        else:
            msg = f"{msg}: {context}"
        self.log_ui(f"⚠ [Async] {msg}", "error")

    # -------------------------------------------------------------------
    # Excel & targets
    # -------------------------------------------------------------------
    def load_excel(self):
        path = filedialog.askopenfilename(filetypes=[("Excel files","*.xlsx")])
        if not path: return
        try:
            import openpyxl
            wb = openpyxl.load_workbook(path)
            sheet = wb.active
            items = []
            mode = self.input_mode.get()
            for row in sheet.iter_rows(values_only=True):
                for cell in row:
                    if cell is not None:
                        s = str(cell).strip()
                        if mode == "phone":
                            s = self._normalize_phone(s)
                            if self.phone_re.match(s):
                                items.append(s)
                        elif mode == "username":
                            if s.startswith("@") and self.username_re.match(s):
                                items.append(s)
                            elif self.username_re.match(s):
                                items.append("@" + s)
                        else:
                            if s.isdigit():
                                items.append(s)
            self.num_text.delete("1.0","end")
            self.num_text.insert("1.0", "\n".join(items))
            self.log_message(f"✔ Loaded {len(items)} targets.")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to read Excel: {e}")

    def clear_targets(self):
        self.num_text.delete("1.0","end")

    def get_targets(self):
        text = self.num_text.get("1.0","end-1c")
        targets = []
        mode = self.input_mode.get()
        for line in text.splitlines():
            line = line.strip()
            if not line: continue
            if mode == "phone":
                line = self._normalize_phone(line)
                if self.phone_re.match(line):
                    targets.append(line)
                else:
                    self.log_message(f"⚠ Skipped invalid phone: {line}", "warn")
            elif mode == "id":
                if self.id_re.match(line):
                    targets.append(line)
                else:
                    self.log_message(f"⚠ Skipped invalid ID: {line}", "warn")
            else:
                if self.username_re.match(line):
                    if not line.startswith("@"):
                        line = "@" + line
                    targets.append(line)
                else:
                    self.log_message(f"⚠ Skipped invalid username: {line}", "warn")
        seen = set()
        unique = []
        for t in targets:
            if t not in seen:
                seen.add(t)
                unique.append(t)
        return unique

    # -------------------------------------------------------------------
    # Login queue
    # -------------------------------------------------------------------
    def _start_login_queue_checker(self):
        self.root.after(100, self._check_login_queue)

    def _check_login_queue(self):
        try:
            while True:
                field_type, prompt, show, future = self.login_helper.queue.get_nowait()
                if field_type == 'phone':
                    val = self._ask_string("Phone", prompt)
                elif field_type == 'code':
                    val = self._ask_string("Code", prompt)
                elif field_type == 'password':
                    val = self._ask_string("Password", prompt, show="*")
                else:
                    val = None
                if self.loop and self.loop.is_running() and not future.done():
                    self.loop.call_soon_threadsafe(future.set_result, val)
        except queue.Empty:
            pass
        finally:
            self.root.after(200, self._check_login_queue)

    # -------------------------------------------------------------------
    # Safe custom dialog with grab handling
    # -------------------------------------------------------------------
    def _ask_string(self, title, prompt, show=None):
        dlg = tk.Toplevel(self.root)
        dlg.title(title)
        dlg.transient(self.root)
        dlg.resizable(False, False)
        dlg.grab_set()  # grab for the dialog

        ttk.Label(dlg, text=prompt, padding=(20,15,20,5)).pack()
        var = tk.StringVar()
        entry = ttk.Entry(dlg, textvariable=var, show=show or "", width=30)
        entry.pack(padx=20, pady=5)
        entry.focus_set()

        result = [None]

        def ok():
            result[0] = var.get()
            self._safe_close_dialog(dlg)
        def cancel():
            result[0] = None
            self._safe_close_dialog(dlg)

        dlg.protocol("WM_DELETE_WINDOW", cancel)
        btn_frame = ttk.Frame(dlg)
        btn_frame.pack(pady=10)
        ttk.Button(btn_frame, text="OK", command=ok).pack(side="left", padx=5)
        ttk.Button(btn_frame, text="Cancel", command=cancel).pack(side="left", padx=5)

        # Bind <Return> and <Escape>
        dlg.bind("<Return>", lambda e: ok())
        dlg.bind("<Escape>", lambda e: cancel())

        # Wait for the dialog to close
        self.root.wait_window(dlg)
        return result[0]

    def _safe_close_dialog(self, dlg):
        """Release grab and destroy dialog, then ensure focus returns to main window."""
        try:
            dlg.grab_release()
        except:
            pass
        try:
            dlg.destroy()
        except:
            pass
        # Force focus back to root to avoid keyboard lock
        try:
            if self.root.winfo_exists():
                self.root.focus_force()
        except:
            pass

    # -------------------------------------------------------------------
    # Start / Stop
    # -------------------------------------------------------------------
    def start_sending(self):
        if self.is_sending: return
        try:
            api_id = int(self.api_id.get())
            if api_id <= 0: raise ValueError
        except (ValueError, tk.TclError):
            messagebox.showerror("Invalid", "Enter valid API ID.")
            return

        api_hash = self.api_hash.get().strip()
        if not api_hash:
            messagebox.showerror("Invalid", "API Hash cannot be empty.")
            return

        min_d = self._get_positive_int(self.min_delay, "Min delay", 0)
        max_d = self._get_positive_int(self.max_delay, "Max delay", 0)
        batch_sz = self._get_positive_int(self.batch_size, "Batch size")
        batch_int = self._get_positive_int(self.batch_interval, "Batch interval")
        retries = self._get_positive_int(self.retry_count, "Retries", 1)
        if None in (min_d, max_d, batch_sz, batch_int, retries):
            return

        if min_d > max_d:
            min_d, max_d = max_d, min_d
            self.min_delay.set(str(min_d))
            self.max_delay.set(str(max_d))
            messagebox.showwarning("Values swapped", "Min delay was larger than Max. Swapped.")

        targets = self.get_targets()
        if not targets:
            messagebox.showwarning("No targets", "Enter valid targets.")
            return
        if not self.accounts:
            messagebox.showwarning("No accounts", "Add at least one account.")
            return

        self._cached_msg = None
        self.targets = deque(targets)
        self.is_sending = True
        self.stop_flag.clear()
        self.start_btn.configure(state="disabled")
        self.stop_btn.configure(state="normal")
        self.export_btn.configure(state="disabled")
        self.progress["maximum"] = len(targets)
        self.progress["value"] = 0
        self.log_message("▶ Starting multi‑account limit tester...", "title")
        self.set_status("Connecting...")
        now_hour = datetime.now().hour
        with self.stats_lock:
            for acc in self.accounts:
                acc["sent_hour"] = 0
                acc["spam_count"] = 0
                acc["blocked"] = False
                acc["last_hour"] = now_hour
                acc["hourly_log"] = []
                acc["target_contact_count"] = 0
                acc["target_total"] = 0
                acc["contact_ratio"] = 0.0
        threading.Thread(target=self._run_async_loop, daemon=True).start()

    def stop_sending(self):
        self.stop_flag.set()
        self.log_message("⏹ Stop requested...", "warn")
        self.stop_btn.configure(state="disabled")
        if self.loop and self.loop.is_running():
            if self.main_task and not self.main_task.done():
                self.loop.call_soon_threadsafe(self.main_task.cancel)
            for task in list(self._send_tasks):
                if not task.done():
                    self.loop.call_soon_threadsafe(task.cancel)
        self.login_helper.cancel_all()

    def _run_async_loop(self):
        self.loop = asyncio.new_event_loop()
        self.loop.set_exception_handler(self._handle_async_exception)
        asyncio.set_event_loop(self.loop)
        main_task = None
        try:
            main_task = self.loop.create_task(self.main_async())
            self.main_task = main_task
            self.loop.run_until_complete(main_task)
        except asyncio.CancelledError:
            pass
        except RuntimeError:
            pass
        finally:
            if main_task and not main_task.done():
                main_task.cancel()
                try:
                    self.loop.run_until_complete(main_task)
                except (asyncio.CancelledError, RuntimeError):
                    pass
            self.loop.close()
            self.loop = None
            self.main_task = None
            self.root.after(0, self._sending_done)

    def _cancel_all_tasks(self):
        """Called from the event loop thread to safely cancel all tasks."""
        for task in asyncio.all_tasks(self.loop):
            task.cancel()

    def on_close(self):
        self.stop_flag.set()
        self.login_helper.cancel_all()
        if self.loop and self.loop.is_running():
            self.loop.call_soon_threadsafe(self._cancel_all_tasks)
            self.loop.call_soon_threadsafe(self.loop.stop)
        self.root.after(400, self.root.destroy)

    def _sending_done(self):
        self.is_sending = False
        self.start_btn.configure(state="normal")
        self.stop_btn.configure(state="disabled")
        self.export_btn.configure(state="normal")
        self.set_status("Ready")
        self.log_message("✔ Finished. You can export CSV now.", "success")
        if self.stats_win:
            self.stats_win.destroy()
            self.stats_win = None

    # -------------------------------------------------------------------
    # Async helpers
    # -------------------------------------------------------------------
    async def _sleep_or_abort(self, seconds):
        for _ in range(int(seconds)):
            if self.stop_flag.is_set():
                return
            await asyncio.sleep(1)
        remainder = seconds - int(seconds)
        if remainder > 0 and not self.stop_flag.is_set():
            await asyncio.sleep(remainder)

    # -------------------------------------------------------------------
    # Main async
    # -------------------------------------------------------------------
    async def main_async(self):
        try:
            api_id = int(self.api_id.get())
            api_hash = self.api_hash.get().strip()
            await self._login_all_accounts(api_id, api_hash)

            active = [acc for acc in self.accounts if acc["authorized"] and not acc["blocked"]]
            if not active:
                self.log_ui("❌ No authorized accounts.")
                return
            self.root.after(0, self._show_stats_window)

            batch_sz = self._get_positive_int(self.batch_size, "Batch size", 1)
            batch_int = self._get_positive_int(self.batch_interval, "Batch interval", 1)
            min_d = self._get_positive_int(self.min_delay, "Min delay", 0)
            max_d = self._get_positive_int(self.max_delay, "Max delay", 0)
            retries = self._get_positive_int(self.retry_count, "Retries", 1)
            if min_d > max_d: min_d, max_d = max_d, min_d

            sem = asyncio.Semaphore(batch_sz)
            sent_total = 0
            account_idx = 0
            self._send_tasks.clear()

            for idx, target in enumerate(self.targets):
                if self.stop_flag.is_set():
                    break
                self._update_hourly_stats()
                active = [acc for acc in self.accounts if acc["authorized"] and not acc["blocked"]]
                if not active:
                    self.log_ui("❌ All accounts blocked.", "error")
                    break

                await sem.acquire()
                if self.stop_flag.is_set():
                    sem.release()
                    break

                acc = active[account_idx % len(active)]
                account_idx += 1
                delay = random.uniform(min_d, max_d)

                task = asyncio.create_task(
                    self._send_with_account_safe(acc, target, delay, sent_total, retries, sem)
                )
                self._send_tasks.add(task)
                sent_total += 1

                if (idx + 1) % batch_sz == 0 and idx + 1 < len(self.targets):
                    await self._sleep_or_abort(batch_int)
                    if self.stop_flag.is_set():
                        break

            if self._send_tasks:
                await asyncio.gather(*self._send_tasks, return_exceptions=True)

            self.log_ui(f"🏁 Done. Total processed: {sent_total}")
            self.status_ui("Finished")
        except asyncio.CancelledError:
            self.log_ui("⏹ Sending cancelled.", "warn")
        finally:
            for acc in self.accounts:
                if acc["client"]:
                    try:
                        await acc["client"].disconnect()
                    except Exception:
                        pass

    async def _send_with_account_safe(self, acc, target, delay, msg_counter, retries, sem):
        """Wrapper that releases the semaphore and cleans up the task set."""
        try:
            return await self._send_with_account(acc, target, delay, msg_counter, retries)
        finally:
            sem.release()
            self._send_tasks.discard(asyncio.current_task())

    async def _login_all_accounts(self, api_id, api_hash):
        for acc in self.accounts:
            if self.stop_flag.is_set():
                break
            masked = self.mask_phone(acc["phone"])
            self.log_ui(f"Connecting {masked}...")
            client = TelegramClient(acc["session"], api_id, api_hash)
            try:
                await client.connect()
                if not await client.is_user_authorized():
                    phone = await self.login_helper.request_phone(
                        f"Phone for {masked} (press Enter to use stored):"
                    )
                    if not phone:
                        phone = acc["phone"]
                    await client.send_code_request(phone)
                    code = await self.login_helper.request_code(f"Code for {masked}:")
                    if not code:
                        self.log_ui(f"❌ Login cancelled for {masked}", "error")
                        acc["authorized"] = False
                        await client.disconnect()
                        continue
                    try:
                        await client.sign_in(phone, code)
                    except SessionPasswordNeededError:
                        pwd = await self.login_helper.request_password(f"2FA for {masked}:")
                        if not pwd:
                            self.log_ui(f"❌ Login cancelled for {masked}", "error")
                            acc["authorized"] = False
                            await client.disconnect()
                            continue
                        await client.sign_in(password=pwd)
                acc["client"] = client
                acc["authorized"] = True
                self.log_ui(f"✔ {masked} logged in.", "success")
            except asyncio.CancelledError:
                self.log_ui(f"❌ Login cancelled for {masked}", "error")
                await client.disconnect()
                break
            except Exception as e:
                self.log_ui(f"❌ Login failed {masked}: {e}", "error")
                acc["authorized"] = False
                await client.disconnect()

    async def _send_with_account(self, acc, target, delay, msg_counter, retries):
        if self.stop_flag.is_set():
            return False
        await asyncio.sleep(delay)
        if self.stop_flag.is_set():
            return False
        msg = self._generate_varied_message(msg_counter)
        mode = self.input_mode.get()
        client = acc["client"]
        masked = self.mask_phone(acc["phone"])

        for attempt in range(retries):
            if self.stop_flag.is_set():
                return False
            try:
                contact_status = await self._dispatch_send(client, target, msg, mode)
                with self.stats_lock:
                    acc["sent_hour"] += 1
                    acc["target_total"] += 1
                    if contact_status is True:
                        acc["target_contact_count"] += 1
                self.log_ui(f"✔ [{masked}] sent to {target}", "success")
                return True
            except FloodWaitError as e:
                self.log_ui(f"⏳ FloodWait {e.seconds}s on {masked}", "warn")
                if e.seconds > 300:
                    with self.stats_lock:
                        acc["blocked"] = True
                    self.log_ui(f"🚫 [{masked}] BLOCKED (long flood)", "spam")
                    return False
                await self._sleep_or_abort(e.seconds)
            except (PeerFloodError, PhoneNumberBannedError, ChatWriteForbiddenError,
                    UserPrivacyRestrictedError, MessageDeleteForbiddenError, ChatAdminRequiredError) as e:
                with self.stats_lock:
                    acc["spam_count"] += 1
                    acc["blocked"] = True
                self.log_ui(f"⛔ [{masked}] SPAM/BLOCK: {type(e).__name__}", "spam")
                return False
            except (OSError, ConnectionError) as e:
                # Network error – never retry to avoid duplicate
                self.log_ui(f"⚠ Network error {masked}: {e} (may have been sent)", "warn")
                try:
                    await client.connect()
                except Exception as ex:
                    self.log_ui(f"❌ [{masked}] Reconnect failed: {ex}", "error")
                with self.stats_lock:
                    acc["blocked"] = True
                return False
            except (UsernameNotOccupiedError, UserIdInvalidError) as e:
                self.log_ui(f"❌ [{masked}] Invalid target: {e}", "error")
                return False
            except Exception as e:
                self.log_ui(f"❌ [{masked}] Unexpected: {e}", "error")
                return False
        self.log_ui(f"⛔ [{masked}] Failed after {retries} retries: {target}", "error")
        return False

    async def _dispatch_send(self, client, target, message, mode):
        # Final stop check before any send
        if self.stop_flag.is_set():
            raise asyncio.CancelledError("Stopped before send")
        if mode == "phone":
            contact = InputPhoneContact(client_id=0, phone=target, first_name="User", last_name="")
            result = await client(ImportContactsRequest([contact]))
            if self.stop_flag.is_set():
                raise asyncio.CancelledError("Stopped before send")
            if not result.users:
                raise UserIdInvalidError("Phone not found")
            user = result.users[0]
            if self.stop_flag.is_set():
                raise asyncio.CancelledError("Stopped before send")
            await client.send_message(user.id, message)
            try:
                await client.delete_contacts([user])
            except Exception as e:
                self.log_ui(f"⚠ Failed to delete contact {target}: {e}", "warn")
            return user.contact
        elif mode == "id":
            uid = int(target.strip())
            if self.stop_flag.is_set():
                raise asyncio.CancelledError("Stopped before send")
            await client.send_message(uid, message)
            return None
        else:
            username = target.strip()
            if not username.startswith("@"):
                username = "@" + username
            entity = await client.get_input_entity(username)
            if self.stop_flag.is_set():
                raise asyncio.CancelledError("Stopped before send")
            await client.send_message(entity, message)
            return None

    def _generate_varied_message(self, counter):
        if self._cached_msg is None:
            self._cached_msg = self.msg_text.get("1.0", "end-1c").strip()
        base = self._cached_msg
        emojis = ["😊","🚀","⭐","🔥","💬","👍","🎉","✨"]
        base = base.replace("{emoji}", random.choice(emojis))
        base = base.replace("{counter}", str(counter))
        if random.random() < 0.5:
            base += " " + random.choice(["", "👍","💪","🙏"])
        return base

    def _update_hourly_stats(self):
        now = datetime.now()
        current_hour = now.hour
        for acc in self.accounts:
            with self.stats_lock:
                if acc["last_hour"] != current_hour:
                    ratio = acc["target_contact_count"] / max(1, acc["target_total"])
                    acc["contact_ratio"] = round(ratio, 2)
                    prev_sent = acc["sent_hour"]
                    acc["hourly_log"].append({
                        "phone": acc["phone"],
                        "hour": acc["last_hour"],
                        "sent": prev_sent,
                        "spam": acc["spam_count"],
                        "blocked": acc["blocked"],
                        "contact_ratio": acc["contact_ratio"],
                        "time": now.strftime("%Y-%m-%d %H:%M:%S")
                    })
                    if len(acc["hourly_log"]) > 24:
                        acc["hourly_log"] = acc["hourly_log"][-24:]
                    acc["sent_hour"] = 0
                    acc["spam_count"] = 0
                    acc["last_hour"] = current_hour
                    acc["target_contact_count"] = 0
                    acc["target_total"] = 0
                    blocked = acc["blocked"]
                    masked = self.mask_phone(acc["phone"])
                    if not blocked:
                        self.log_ui(f"🕒 [{masked}] Hourly reset, prev sent={prev_sent}")

    # -------------------------------------------------------------------
    # CSV Export
    # -------------------------------------------------------------------
    def export_csv(self):
        if self.is_sending:
            messagebox.showwarning("Wait", "Stop sending first.")
            return
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV files","*.csv")])
        if not path: return
        try:
            with open(path, "w", newline="", encoding="utf-8") as f:
                writer = csv.writer(f)
                writer.writerow(["phone", "hour", "sent", "spam", "blocked", "contact_ratio", "time"])
                has_data = False
                for acc in self.accounts:
                    with self.stats_lock:
                        for entry in acc["hourly_log"]:
                            writer.writerow([
                                entry["phone"], entry["hour"], entry["sent"],
                                entry["spam"], entry["blocked"], entry["contact_ratio"],
                                entry["time"]
                            ])
                            has_data = True
                if not has_data:
                    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    for acc in self.accounts:
                        writer.writerow([
                            acc["phone"], "current", acc["sent_hour"],
                            acc["spam_count"], acc["blocked"], acc["contact_ratio"],
                            now
                        ])
            self.log_message(f"📊 Exported stats to {path}", "success")
        except Exception as e:
            messagebox.showerror("Export failed", str(e))

    # -------------------------------------------------------------------
    # Stats window
    # -------------------------------------------------------------------
    def _show_stats_window(self):
        if self.stats_win:
            return
        win = tk.Toplevel(self.root)
        win.title("Live Account Stats")
        win.geometry("650x400")
        def on_close():
            self.stats_win = None
            win.destroy()
        win.protocol("WM_DELETE_WINDOW", on_close)
        self.stats_win = win
        self.stats_text = scrolledtext.ScrolledText(win, state="normal", wrap="word")
        self.stats_text.pack(fill="both", expand=True)
        self._refresh_stats()

    def _refresh_stats(self):
        if not self.stats_win or not self.stats_win.winfo_exists():
            self.stats_win = None
            return
        try:
            self.stats_text.configure(state="normal")
            self.stats_text.delete("1.0", "end")
            with self.stats_lock:
                for acc in self.accounts:
                    masked = self.mask_phone(acc["phone"])
                    line = (f"{masked}: sent/h={acc['sent_hour']}, spam={acc['spam_count']}, "
                            f"blocked={acc['blocked']}, ratio={acc['contact_ratio']}\n")
                    if acc["hourly_log"]:
                        last = acc["hourly_log"][-1]
                        line += f"   Last hour: sent={last['sent']}, spam={last['spam']}, blocked={last['blocked']}, ratio={last['contact_ratio']}\n"
                    self.stats_text.insert("end", line)
            self.stats_text.configure(state="disabled")
        except tk.TclError:
            pass
        finally:
            self.root.after(5000, self._refresh_stats)

# -------------------------------------------------------------------
# Entry point
# -------------------------------------------------------------------
if __name__ == "__main__":
    root = tk.Tk()
    app = TelegramSenderApp(root)
    root.mainloop()