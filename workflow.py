import json
import math
import os
import tempfile
import tkinter as tk
from tkinter import filedialog, messagebox
from tkinter import font as tkfont


class CompactFlowCanvas:
    """单文件紧凑流程图编辑器：自由气泡、虚线箭头、自动保存、快速生长、注释悬浮、三步撤销。"""

    CANVAS_BG = "#ffffff"
    NODE_MIN_W = 54
    NODE_MIN_H = 26
    NODE_PAD_X = 16
    NODE_PAD_Y = 8
    NODE_MAX_TEXT_W = 260
    NODE_RADIUS = 13
    NODE_OUTLINE = "#777777"
    NODE_SELECTED_OUTLINE = "#1677ff"
    NOTE_BORDER = "#d00000"
    NOTE_LINE = "#d00000"
    NOTE_BG = "#fff8d8"
    NOTE_EDITOR_W = 300
    NOTE_EDITOR_H = 180
    NOTE_MIN_W = 160
    NOTE_MIN_H = 70
    NOTE_RESIZE_HIT = 8

    EDGE_COLORS = ["#000000", "#d00000", "#008000", "#0057ff", "#7a1fd1"]
    EDGE_SELECTED = "#1677ff"
    EDGE_DASH = (4, 3)
    EDGE_WIDTH = 2
    EDGE_HIT_W = 14
    EDGE_PARALLEL_GAP = 7
    HANDLE_R = 5
    DRAG_START_PX = 4
    SNAP_THRESHOLD = 8
    # 5px 距离网格不要太强；越小越不容易被强制吸走。
    SNAP_DISTANCE_THRESHOLD = 1.4
    SNAP_GUIDE_COLOR = "#bdbdbd"

    AUTOSAVE_MS = 60_000

    def __init__(self, root):
        self.root = root
        self.root.title("紧凑行动与决策流程图")
        self.root.geometry("1200x760")

        self.nodes = {}
        self.edges = {}
        self.depths = {}
        self.next_node_id = 1
        self.next_edge_id = 1

        self.selected_kind = None
        self.selected_id = None
        self.selected_ids = set()

        self.mode = None
        self.drag_node_id = None
        self.drag_offset = (0, 0)
        self.drag_group_ids = []
        self.drag_group_anchor_id = None
        self.drag_group_original = {}
        self.drag_start_canvas = None
        self.selection_rect = None
        self.lasso_start = None
        self.right_source_id = None
        self.right_start = None
        self.right_dragging = False
        self.temp_line_id = None
        self.rewire = None
        self.handle_items = []
        self.snap_enabled = tk.BooleanVar(value=True)
        self.snap_guides = []

        self.entry = None
        self.entry_window = None
        self.edit_node_id = None
        self.edit_original_text = ""

        self.note_popup_items = []
        self.note_popup_node_id = None
        self.note_editor = None
        self.note_editor_undo_snapshot = None
        self.hover_node_id = None

        self.script_dir = os.path.dirname(os.path.abspath(__file__))
        self.autosave_path = os.path.join(self.script_dir, "workflow.json")
        self.file_path = self.autosave_path
        self.autosave_job = None

        self.undo_stack = []
        self.is_restoring_undo = False
        self.drag_undo_recorded = False
        self.edit_undo_snapshot = None

        self.font = tkfont.Font(family="Arial", size=10)
        self.small_font = tkfont.Font(family="Arial", size=9)

        self._build_ui()
        self._bind_events()
        self.canvas.focus_set()
        self.load_default_workflow_if_exists()
        self.schedule_autosave()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    # ---------- UI ----------
    def _build_ui(self):
        top = tk.Frame(self.root)
        top.pack(side=tk.TOP, fill=tk.X)

        tk.Button(top, text="保存 Ctrl+S", command=self.save_flow).pack(side=tk.LEFT, padx=(6, 2), pady=4)
        tk.Button(top, text="另存", command=lambda: self.save_flow(save_as=True)).pack(side=tk.LEFT, padx=2, pady=4)
        tk.Button(top, text="打开 Ctrl+O", command=self.load_flow).pack(side=tk.LEFT, padx=2, pady=4)
        tk.Button(top, text="清空", command=self.clear_all_confirm).pack(side=tk.LEFT, padx=2, pady=4)
        tk.Checkbutton(top, text="Snap辅助", variable=self.snap_enabled).pack(side=tk.LEFT, padx=(8, 2), pady=4)

        self.status = tk.Label(
            top,
            anchor="w",
            text="空白左键=新气泡；先单击选中再拖动=移动；Ctrl+左键拖框=多选；Snap轻吸附对齐；右键拖气泡=虚线箭头；右键轻点气泡=注释。",
        )
        self.status.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=8)

        outer = tk.Frame(self.root)
        outer.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        self.canvas = tk.Canvas(
            outer,
            bg=self.CANVAS_BG,
            highlightthickness=0,
            scrollregion=(-5000, -5000, 5000, 5000),
        )
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        ybar = tk.Scrollbar(outer, orient=tk.VERTICAL, command=self.canvas.yview)
        ybar.pack(side=tk.RIGHT, fill=tk.Y)
        xbar = tk.Scrollbar(self.root, orient=tk.HORIZONTAL, command=self.canvas.xview)
        xbar.pack(side=tk.BOTTOM, fill=tk.X)
        self.canvas.configure(xscrollcommand=xbar.set, yscrollcommand=ybar.set)

        self.canvas.xview_moveto(0.5)
        self.canvas.yview_moveto(0.5)

    def _bind_events(self):
        self.canvas.bind("<Button-1>", self.on_left_down)
        self.canvas.bind("<B1-Motion>", self.on_left_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_left_up)
        self.canvas.bind("<Double-Button-1>", self.on_double_left)

        self.canvas.bind("<Button-3>", self.on_right_down)
        self.canvas.bind("<B3-Motion>", self.on_right_drag)
        self.canvas.bind("<ButtonRelease-3>", self.on_right_up)
        self.canvas.bind("<Double-Button-3>", self.on_right_double)

        # macOS / 部分触控板兼容：中键拖动画布。
        self.canvas.bind("<Button-2>", self.on_middle_down)
        self.canvas.bind("<B2-Motion>", self.on_middle_drag)

        self.canvas.bind("<Motion>", self.on_canvas_motion)
        self.canvas.bind("<Leave>", lambda e: self.hide_note_popup())

        # 注释编辑框打开时，点到画板/工具栏/窗口其他区域都保存并关闭。
        self.root.bind("<Button-1>", self.on_global_left_click, add="+")
        self.root.bind("<Button-3>", self.on_global_right_click, add="+")

        self.root.bind("<Delete>", self.delete_selected)
        self.root.bind("<BackSpace>", self.delete_selected)
        self.root.bind("<Control-s>", lambda e: self.save_flow())
        self.root.bind("<Control-o>", lambda e: self.load_flow())
        self.root.bind("<Control-z>", self.undo_last)
        self.root.bind("<Control-Z>", self.undo_last)
        self.root.bind("<Escape>", self.cancel_current_action)
        self.root.bind("<Tab>", self.on_tab_key)
        self.root.bind("<Return>", self.on_return_key)
        self.root.bind("<KP_Enter>", self.on_return_key)

        self.canvas.bind("<MouseWheel>", self.on_mouse_wheel)
        self.canvas.bind("<Shift-MouseWheel>", self.on_shift_mouse_wheel)

    def cx(self, event):
        return self.canvas.canvasx(event.x)

    def cy(self, event):
        return self.canvas.canvasy(event.y)

    def on_middle_down(self, event):
        self.canvas.scan_mark(event.x, event.y)

    def on_middle_drag(self, event):
        self.canvas.scan_dragto(event.x, event.y, gain=1)

    def on_mouse_wheel(self, event):
        self.canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")

    def on_shift_mouse_wheel(self, event):
        self.canvas.xview_scroll(int(-1 * (event.delta / 120)), "units")

    # ---------- 节点 ----------
    def create_node(self, x, y, text="", note=""):
        nid = self.next_node_id
        self.next_node_id += 1
        self.nodes[nid] = {
            "id": nid,
            "x": float(x),  # 左上角；文字增长时永远不移动这个 x。
            "y": float(y),
            "text": text,
            "note": note,
            "note_w": self.NOTE_EDITOR_W,
            "note_h": self.NOTE_EDITOR_H,
            "w": self.NODE_MIN_W,
            "h": self.NODE_MIN_H,
            "body": None,
            "text_item": None,
            "note_item": None,
        }
        self.depths.setdefault(nid, 0)
        self.redraw_node(nid)
        self.select("node", nid)
        return nid

    def redraw_node(self, nid):
        if nid not in self.nodes:
            return
        node = self.nodes[nid]
        for key in ("body", "text_item", "note_item"):
            item = node.get(key)
            if item:
                self.canvas.delete(item)
                node[key] = None

        wrapped, w, h = self.measure_node(node.get("text", ""))
        node["w"] = w
        node["h"] = h
        x1, y1 = node["x"], node["y"]
        x2, y2 = x1 + w, y1 + h
        r = min(self.NODE_RADIUS, h / 2)
        fill = self.color_for_depth(self.depths.get(nid, 0))
        selected = self.node_is_selected(nid)
        has_note = bool(str(node.get("note", "")).strip())
        if has_note:
            outline = self.NOTE_BORDER
            width = 3
        else:
            outline = self.NODE_SELECTED_OUTLINE if selected else self.NODE_OUTLINE
            width = 2 if selected else 1

        body = self.create_round_rect(x1, y1, x2, y2, r, fill=fill, outline=outline, width=width)
        self.canvas.addtag_withtag("node", body)
        self.canvas.addtag_withtag(f"node:{nid}", body)
        self.canvas.addtag_withtag("body", body)

        text_item = self.canvas.create_text(
            x1 + w / 2,
            y1 + h / 2,
            text=wrapped if wrapped.strip() else " ",
            fill="#111111",
            font=self.font,
            tags=("node", f"node:{nid}", "node_text"),
            justify=tk.CENTER,
        )

        # 有注释的节点用 3px 红色边框直接标记，不再额外画右上角蓝色小角标。
        note_item = None

        node["body"] = body
        node["text_item"] = text_item
        node["note_item"] = note_item
        self.raise_nodes()
        self.raise_handles()
        if self.entry_window is not None:
            self.canvas.tag_raise(self.entry_window)

    def create_round_rect(self, x1, y1, x2, y2, r, **kwargs):
        points = [
            x1 + r, y1,
            x2 - r, y1,
            x2, y1,
            x2, y1 + r,
            x2, y2 - r,
            x2, y2,
            x2 - r, y2,
            x1 + r, y2,
            x1, y2,
            x1, y2 - r,
            x1, y1 + r,
            x1, y1,
        ]
        return self.canvas.create_polygon(points, smooth=True, splinesteps=12, **kwargs)

    def measure_node(self, text):
        text = "" if text is None else str(text)
        lines = self.wrap_text_by_pixels(text, self.NODE_MAX_TEXT_W)
        if not lines:
            lines = [""]
        max_line_w = max(self.font.measure(line) for line in lines) if lines else 0
        line_h = self.font.metrics("linespace")
        w = max(self.NODE_MIN_W, max_line_w + self.NODE_PAD_X * 2)
        w = min(w, self.NODE_MAX_TEXT_W + self.NODE_PAD_X * 2)
        h = max(self.NODE_MIN_H, len(lines) * line_h + self.NODE_PAD_Y)
        return "\n".join(lines), w, h

    def wrap_text_by_pixels(self, text, max_px):
        lines = []
        current = ""
        for ch in text:
            if ch == "\n":
                lines.append(current)
                current = ""
                continue
            candidate = current + ch
            if self.font.measure(candidate) <= max_px or not current:
                current = candidate
            else:
                lines.append(current)
                current = ch
        lines.append(current)
        return lines

    def color_for_depth(self, depth):
        t = max(0, min(10, int(depth))) / 10.0
        r = 255
        g = int(255 - 165 * t)
        b = int(255 - 165 * t)
        return f"#{r:02x}{g:02x}{b:02x}"

    def raise_nodes(self):
        for node in self.nodes.values():
            for key in ("body", "text_item", "note_item"):
                item = node.get(key)
                if item:
                    self.canvas.tag_raise(item)

    # ---------- 边 ----------
    def create_edge(self, source, target):
        if source not in self.nodes or target not in self.nodes or source == target:
            return None
        eid = self.next_edge_id
        self.next_edge_id += 1
        self.edges[eid] = {"id": eid, "source": source, "target": target, "hit": None, "line": None}
        self.recompute_depths()
        self.redraw_all_edges()
        self.select("edge", eid)
        return eid

    def redraw_edge(self, eid):
        if eid not in self.edges:
            return
        edge = self.edges[eid]
        for key in ("hit", "line"):
            item = edge.get(key)
            if item:
                self.canvas.delete(item)
                edge[key] = None

        if edge["source"] not in self.nodes or edge["target"] not in self.nodes:
            return
        x1, y1, x2, y2 = self.edge_display_points(eid)
        color = self.edge_color(eid)

        # 不可见粗点击层：视觉仍是 2px 虚线，点击区域更宽。
        hit = self.canvas.create_line(
            x1, y1, x2, y2,
            fill=self.CANVAS_BG,
            width=self.EDGE_HIT_W,
            capstyle=tk.ROUND,
            tags=("edge", f"edge:{eid}", "edge_hit"),
        )
        line = self.canvas.create_line(
            x1, y1, x2, y2,
            fill=color,
            width=self.EDGE_WIDTH,
            arrow=tk.LAST,
            arrowshape=(10, 12, 4),
            capstyle=tk.ROUND,
            dash=self.EDGE_DASH,
            tags=("edge", f"edge:{eid}", "edge_line"),
        )
        edge["hit"] = hit
        edge["line"] = line
        self.canvas.tag_lower(hit)
        self.canvas.tag_raise(line, hit)
        self.raise_nodes()
        self.raise_handles()

    def redraw_all_edges(self):
        for eid in list(self.edges.keys()):
            self.redraw_edge(eid)
        self.show_edge_handles_if_needed()

    def edge_points(self, source_id, target_id):
        a = self.nodes[source_id]
        b = self.nodes[target_id]
        ax, ay = a["x"] + a["w"] / 2, a["y"] + a["h"] / 2
        bx, by = b["x"] + b["w"] / 2, b["y"] + b["h"] / 2
        dx, dy = bx - ax, by - ay
        if abs(dx) < 0.001 and abs(dy) < 0.001:
            return ax, ay, bx, by
        sx, sy = self.boundary_point(a, dx, dy)
        tx, ty = self.boundary_point(b, -dx, -dy)
        return sx, sy, tx, ty

    def boundary_point(self, node, dx, dy):
        cx = node["x"] + node["w"] / 2
        cy = node["y"] + node["h"] / 2
        hw = node["w"] / 2
        hh = node["h"] / 2
        if abs(dx) < 0.001:
            scale = hh / max(abs(dy), 0.001)
        elif abs(dy) < 0.001:
            scale = hw / max(abs(dx), 0.001)
        else:
            scale = min(hw / abs(dx), hh / abs(dy))
        return cx + dx * scale, cy + dy * scale

    def edge_overlap_group(self, eid):
        if eid not in self.edges:
            return [], 0
        edge = self.edges[eid]
        key = tuple(sorted((edge["source"], edge["target"])))
        group = [
            other_id for other_id, other in self.edges.items()
            if tuple(sorted((other["source"], other["target"]))) == key
        ]
        group.sort()
        return group, group.index(eid) if eid in group else 0

    def edge_color(self, eid):
        group, index = self.edge_overlap_group(eid)
        if len(group) <= 1:
            return self.EDGE_COLORS[0]
        return self.EDGE_COLORS[index % len(self.EDGE_COLORS)]

    def edge_display_points(self, eid):
        edge = self.edges[eid]
        x1, y1, x2, y2 = self.edge_points(edge["source"], edge["target"])
        group, index = self.edge_overlap_group(eid)
        if len(group) <= 1:
            return x1, y1, x2, y2

        mid = (len(group) - 1) / 2
        offset = (index - mid) * self.EDGE_PARALLEL_GAP
        dx, dy = x2 - x1, y2 - y1
        length = math.hypot(dx, dy)
        if length < 0.001:
            return x1, y1, x2, y2
        nx, ny = -dy / length, dx / length
        return x1 + nx * offset, y1 + ny * offset, x2 + nx * offset, y2 + ny * offset

    def redraw_edges_for_node(self, nid):
        for eid, edge in list(self.edges.items()):
            if edge["source"] == nid or edge["target"] == nid:
                self.redraw_edge(eid)
        self.show_edge_handles_if_needed()

    def recompute_depths(self):
        # 有环时也不会卡死；深度只需要 0-10 的可视化强度。
        depths = {nid: 0 for nid in self.nodes}
        for _ in range(10):
            changed = False
            for e in self.edges.values():
                s, t = e["source"], e["target"]
                if s in depths and t in depths:
                    nd = min(10, depths[s] + 1)
                    if nd > depths[t]:
                        depths[t] = nd
                        changed = True
            if not changed:
                break
        self.depths = depths
        for nid in list(self.nodes.keys()):
            self.redraw_node(nid)
        self.redraw_all_edges()

    # ---------- 选择与命中 ----------
    def node_is_selected(self, nid):
        if self.selected_kind == "node":
            return self.selected_id == nid
        if self.selected_kind == "nodes":
            return nid in self.selected_ids
        return False

    def select(self, kind, item_id):
        self.commit_edit_if_active()
        old_node_ids = self.get_selected_node_ids()
        old_kind, old_id = self.selected_kind, self.selected_id
        self.selected_kind, self.selected_id = kind, item_id
        self.selected_ids = {item_id} if kind == "node" and item_id in self.nodes else set()
        for nid in old_node_ids | self.get_selected_node_ids():
            if nid in self.nodes:
                self.redraw_node(nid)
        if old_kind == "edge" and old_id in self.edges:
            self.redraw_edge(old_id)
        if kind == "node" and item_id in self.nodes:
            self.redraw_node(item_id)
            self.clear_handles()
            self.status.config(text="已选中气泡：再次按住拖动可移动；双击编辑文字；右键轻点编辑注释；Tab/Enter 快速生成；Delete 删除。")
        elif kind == "edge" and item_id in self.edges:
            self.redraw_edge(item_id)
            self.show_edge_handles_if_needed()
            self.status.config(text="已选中箭头：拖蓝色端点到另一个气泡可重连；Delete 删除这条线。")
        else:
            self.clear_handles()
            self.status.config(text="空白左键=新气泡；Ctrl+左键拖框=多选；先选中再拖动=移动；右键拖气泡=连虚线箭头；右键轻点=注释。")

    def get_selected_node_ids(self):
        if self.selected_kind == "node" and self.selected_id in self.nodes:
            return {self.selected_id}
        if self.selected_kind == "nodes":
            return {nid for nid in self.selected_ids if nid in self.nodes}
        return set()

    def select_nodes(self, node_ids):
        self.commit_edit_if_active()
        old_node_ids = self.get_selected_node_ids()
        self.selected_ids = {nid for nid in node_ids if nid in self.nodes}
        if len(self.selected_ids) == 1:
            self.selected_kind = "node"
            self.selected_id = next(iter(self.selected_ids))
        elif self.selected_ids:
            self.selected_kind = "nodes"
            self.selected_id = None
        else:
            self.selected_kind = None
            self.selected_id = None
            self.selected_ids = set()
        for nid in old_node_ids | self.get_selected_node_ids():
            if nid in self.nodes:
                self.redraw_node(nid)
        self.clear_handles()
        if self.selected_kind == "nodes":
            self.status.config(text=f"已框选 {len(self.selected_ids)} 个气泡：拖其中任意一个可整体移动；Delete 批量删除；Ctrl+Z 撤销。")
        elif self.selected_kind == "node":
            self.status.config(text="已选中气泡：再次按住拖动可移动；双击编辑文字；右键轻点编辑注释；Tab/Enter 快速生成；Delete 删除。")
        else:
            self.status.config(text="未选中气泡。")

    def clear_selection(self):
        old_node_ids = self.get_selected_node_ids()
        old_kind, old_id = self.selected_kind, self.selected_id
        self.selected_kind, self.selected_id = None, None
        self.selected_ids = set()
        for nid in old_node_ids:
            if nid in self.nodes:
                self.redraw_node(nid)
        if old_kind == "edge" and old_id in self.edges:
            self.redraw_edge(old_id)
        self.clear_handles()

    def item_node_id(self, item):
        for tag in self.canvas.gettags(item):
            if tag.startswith("node:"):
                try:
                    return int(tag.split(":", 1)[1])
                except ValueError:
                    pass
        return None

    def item_edge_id(self, item):
        for tag in self.canvas.gettags(item):
            if tag.startswith("edge:"):
                try:
                    return int(tag.split(":", 1)[1])
                except ValueError:
                    pass
        return None

    def item_handle(self, item):
        for tag in self.canvas.gettags(item):
            if tag.startswith("handle:"):
                _, eid, endpoint = tag.split(":")
                return int(eid), endpoint
        return None

    def get_top_item_data(self, x, y):
        items = self.canvas.find_overlapping(x - 7, y - 7, x + 7, y + 7)
        for item in reversed(items):
            handle = self.item_handle(item)
            if handle:
                return "handle", handle
        for item in reversed(items):
            nid = self.item_node_id(item)
            if nid is not None and nid in self.nodes:
                return "node", nid
        for item in reversed(items):
            eid = self.item_edge_id(item)
            if eid is not None and eid in self.edges:
                return "edge", eid
        return None, None

    def node_at(self, x, y):
        kind, data = self.get_top_item_data(x, y)
        return data if kind == "node" else None

    # ---------- 鼠标动作 ----------
    def is_ctrl_down(self, event):
        return bool(getattr(event, "state", 0) & 0x0004)

    def on_left_down(self, event):
        was_editing = self.entry is not None
        self.canvas.focus_set()
        x, y = self.cx(event), self.cy(event)

        if self.note_editor is not None:
            zone = self.note_editor_zone(x, y)
            if zone in {"right", "bottom", "corner"}:
                self.start_note_resize(zone, x, y)
                return "break"
            if zone == "inside":
                return "break"
            self.close_note_editor(save=True)
            return "break"

        if was_editing and self.entry is not None:
            self.commit_edit_if_active()

        # Ctrl + 左键拖拽：方框多选。无论从空白还是从气泡上开始，都优先进入框选。
        if self.is_ctrl_down(event):
            self.start_lasso_select(x, y)
            return "break"

        kind, data = self.get_top_item_data(x, y)
        if kind == "handle":
            eid, endpoint = data
            self.select("edge", eid)
            self.start_rewire(eid, endpoint, x, y)
            return
        if kind == "node":
            nid = data
            already_selected = self.node_is_selected(nid)
            if not already_selected:
                self.select("node", nid)
                self.mode = None
                self.drag_node_id = None
                return

            # 已经处于选中状态时，再次按住拖拽才允许移动。
            # 单选移动一个；多选时拖任意一个已选中气泡，整体移动。
            if self.selected_kind == "nodes" and nid in self.selected_ids:
                self.start_group_drag(nid, x, y)
            else:
                self.select("node", nid)
                self.start_single_drag(nid, x, y)
            return
        if kind == "edge":
            self.select("edge", data)
            self.mode = None
            return

        # 如果刚才只是为了结束编辑而点空白，不再顺手生成一个新的空气泡。
        if was_editing:
            self.mode = None
            return

        self.record_undo()
        nid = self.create_node(x, y, "")
        self.mode = None
        self.start_edit_node(nid, select_all=True)

    def start_single_drag(self, nid, x, y):
        if nid not in self.nodes:
            return
        node = self.nodes[nid]
        self.mode = "drag_node"
        self.drag_node_id = nid
        self.drag_offset = (node["x"] - x, node["y"] - y)
        self.drag_start_canvas = (x, y)
        self.drag_undo_recorded = False

    def start_group_drag(self, anchor_id, x, y):
        ids = sorted(self.get_selected_node_ids())
        if anchor_id not in ids:
            ids.append(anchor_id)
        self.mode = "drag_group"
        self.drag_group_ids = ids
        self.drag_group_anchor_id = anchor_id
        self.drag_group_original = {nid: (self.nodes[nid]["x"], self.nodes[nid]["y"]) for nid in ids if nid in self.nodes}
        self.drag_start_canvas = (x, y)
        self.drag_undo_recorded = False

    def on_left_drag(self, event):
        x, y = self.cx(event), self.cy(event)
        if self.mode == "note_resize":
            self.update_note_resize(x, y)
            return "break"
        if self.mode == "lasso":
            self.update_lasso_select(x, y)
            return "break"
        if self.mode == "drag_node" and self.drag_node_id in self.nodes:
            nid = self.drag_node_id
            ox, oy = self.drag_offset
            raw_x = x + ox
            raw_y = y + oy
            new_x, new_y = self.apply_snap_for_node(nid, raw_x, raw_y)
            if not self.drag_undo_recorded and (abs(self.nodes[nid]["x"] - new_x) > 0.1 or abs(self.nodes[nid]["y"] - new_y) > 0.1):
                self.record_undo()
                self.drag_undo_recorded = True
            self.nodes[nid]["x"] = new_x
            self.nodes[nid]["y"] = new_y
            self.redraw_node(nid)
            self.redraw_edges_for_node(nid)
            self.hide_note_popup()
        elif self.mode == "drag_group" and self.drag_group_anchor_id in self.nodes and self.drag_start_canvas:
            sx, sy = self.drag_start_canvas
            dx, dy = x - sx, y - sy
            anchor = self.drag_group_anchor_id
            if anchor not in self.drag_group_original:
                return
            ax0, ay0 = self.drag_group_original[anchor]
            raw_ax, raw_ay = ax0 + dx, ay0 + dy
            snap_ax, snap_ay = self.apply_snap_for_node(anchor, raw_ax, raw_ay, ignore_ids=set(self.drag_group_ids))
            dx += snap_ax - raw_ax
            dy += snap_ay - raw_ay
            if not self.drag_undo_recorded and (abs(dx) > 0.1 or abs(dy) > 0.1):
                self.record_undo()
                self.drag_undo_recorded = True
            for nid, (ox0, oy0) in self.drag_group_original.items():
                if nid in self.nodes:
                    self.nodes[nid]["x"] = ox0 + dx
                    self.nodes[nid]["y"] = oy0 + dy
                    self.redraw_node(nid)
            for nid in list(self.drag_group_original.keys()):
                if nid in self.nodes:
                    self.redraw_edges_for_node(nid)
            self.hide_note_popup()
        elif self.mode == "rewire" and self.rewire:
            self.update_rewire_temp(x, y)

    def on_left_up(self, event):
        x, y = self.cx(event), self.cy(event)
        if self.mode == "note_resize":
            self.finish_note_resize()
        elif self.mode == "lasso":
            self.finish_lasso_select(x, y)
        elif self.mode == "rewire" and self.rewire:
            self.finish_rewire(x, y)
        self.mode = None
        self.drag_node_id = None
        self.drag_group_ids = []
        self.drag_group_anchor_id = None
        self.drag_group_original = {}
        self.drag_start_canvas = None
        self.drag_undo_recorded = False
        self.clear_snap_guides()

    # ---------- 框选 / Snap辅助 ----------
    def start_lasso_select(self, x, y):
        self.commit_edit_if_active()
        self.clear_snap_guides()
        self.mode = "lasso"
        self.lasso_start = (x, y)
        if self.selection_rect is not None:
            self.canvas.delete(self.selection_rect)
        self.selection_rect = self.canvas.create_rectangle(
            x, y, x, y,
            outline=self.EDGE_SELECTED,
            width=1,
            dash=(3, 2),
            fill="",
            tags=("selection_rect",),
        )
        self.status.config(text="正在框选：松开左键后选中框内/相交的气泡。")

    def update_lasso_select(self, x, y):
        if self.mode != "lasso" or self.lasso_start is None:
            return
        x0, y0 = self.lasso_start
        if self.selection_rect is not None:
            self.canvas.coords(self.selection_rect, x0, y0, x, y)

    def finish_lasso_select(self, x, y):
        if self.lasso_start is None:
            return
        x0, y0 = self.lasso_start
        rx1, rx2 = sorted((x0, x))
        ry1, ry2 = sorted((y0, y))
        selected = []
        # 框太小就视为取消，避免 Ctrl+轻点把当前选择清掉。
        if abs(rx2 - rx1) >= 3 or abs(ry2 - ry1) >= 3:
            for nid, n in self.nodes.items():
                if self.node_rect_intersects(n, rx1, ry1, rx2, ry2):
                    selected.append(nid)
        if self.selection_rect is not None:
            self.canvas.delete(self.selection_rect)
            self.selection_rect = None
        self.lasso_start = None
        self.select_nodes(selected)

    def node_rect_intersects(self, node, rx1, ry1, rx2, ry2):
        nx1, ny1 = node["x"], node["y"]
        nx2, ny2 = nx1 + node["w"], ny1 + node["h"]
        return not (nx2 < rx1 or nx1 > rx2 or ny2 < ry1 or ny1 > ry2)

    def apply_snap_for_node(self, nid, raw_x, raw_y, ignore_ids=None):
        if ignore_ids is None:
            ignore_ids = {nid}
        else:
            ignore_ids = set(ignore_ids) | {nid}
        self.clear_snap_guides()
        if not self.snap_enabled.get() or nid not in self.nodes:
            return raw_x, raw_y

        n = self.nodes[nid]
        align_threshold = self.SNAP_THRESHOLD
        distance_threshold = self.SNAP_DISTANCE_THRESHOLD
        best_x = None
        best_x_dist = align_threshold + 0.001
        best_y = None
        best_y_dist = align_threshold + 0.001
        raw_center_y = raw_y + n["h"] / 2

        # “左边最近的气泡”：只拿当前气泡左边、右边界最靠近 raw_x 的那一个，
        # 然后把两者水平间距轻微吸附到 5px 的倍数。
        nearest_left_right_edge = None

        for oid, other in self.nodes.items():
            if oid in ignore_ids:
                continue
            # 上下结构常用：左边界对齐。只在非常接近时轻微吸附。
            dx = abs(raw_x - other["x"])
            if dx < best_x_dist:
                best_x_dist = dx
                best_x = other["x"]

            other_right = other["x"] + other["w"]
            if other_right <= raw_x:
                if nearest_left_right_edge is None or other_right > nearest_left_right_edge:
                    nearest_left_right_edge = other_right

            # 左右结构常用：气泡垂直中线/中心线对齐。
            other_center_y = other["y"] + other["h"] / 2
            dy = abs(raw_center_y - other_center_y)
            if dy < best_y_dist:
                best_y_dist = dy
                best_y = other_center_y - n["h"] / 2

        # 对“与左边最近气泡的间距”做 5px 倍数轻吸附。这个阈值很小，
        # 所以只有已经接近 5px 倍数时才吸过去，不会强行牵引。
        if nearest_left_right_edge is not None:
            gap = raw_x - nearest_left_right_edge
            snapped_gap = round(gap / 5.0) * 5.0
            snapped_x = nearest_left_right_edge + snapped_gap
            dist = abs(snapped_x - raw_x)
            if dist <= distance_threshold and dist < best_x_dist:
                best_x = snapped_x
                best_x_dist = dist

        new_x = best_x if best_x is not None and best_x_dist <= align_threshold else raw_x
        new_y = best_y if best_y is not None and best_y_dist <= align_threshold else raw_y
        self.draw_snap_guides(new_x if abs(new_x - raw_x) > 0.001 else None, (new_y + n["h"] / 2) if abs(new_y - raw_y) > 0.001 else None)
        return new_x, new_y

    def draw_snap_guides(self, x=None, y=None):
        self.clear_snap_guides()
        if x is not None:
            self.snap_guides.append(self.canvas.create_line(
                x, -5000, x, 5000, fill=self.SNAP_GUIDE_COLOR, width=1, dash=(2, 4), tags=("snap_guide",)
            ))
        if y is not None:
            self.snap_guides.append(self.canvas.create_line(
                -5000, y, 5000, y, fill=self.SNAP_GUIDE_COLOR, width=1, dash=(2, 4), tags=("snap_guide",)
            ))
        for item in self.snap_guides:
            self.canvas.tag_lower(item)
        for e in self.edges.values():
            for key in ("hit", "line"):
                item = e.get(key)
                if item:
                    self.canvas.tag_raise(item)
        self.raise_nodes()
        self.raise_handles()

    def clear_snap_guides(self):
        for item in self.snap_guides:
            try:
                self.canvas.delete(item)
            except tk.TclError:
                pass
        self.snap_guides = []

    def on_double_left(self, event):
        x, y = self.cx(event), self.cy(event)
        kind, data = self.get_top_item_data(x, y)
        if kind == "node":
            self.start_edit_node(data, select_all=True)

    def on_right_down(self, event):
        # 右键轻点注释和右键拖拽连线必须分离：
        # 按下时只记录“待定右键操作”，只有拖动超过阈值才真正创建临时线。
        was_editing = self.entry is not None
        self.canvas.focus_set()
        if was_editing and self.entry is not None:
            self.commit_edit_if_active()
        x, y = self.cx(event), self.cy(event)
        if self.note_editor is not None:
            zone = self.note_editor_zone(x, y)
            if zone == "inside" or zone in {"right", "bottom", "corner"}:
                return "break"
            self.close_note_editor(save=True)
            return "break"
        kind, data = self.get_top_item_data(x, y)
        self.right_source_id = None
        self.right_start = None
        self.right_dragging = False
        if self.temp_line_id is not None:
            self.canvas.delete(self.temp_line_id)
            self.temp_line_id = None
        if kind == "node" and data in self.nodes:
            self.right_source_id = data
            self.right_start = (x, y)
            self.select("node", data)
            self.status.config(text="右键拖动到另一个气泡=建立关联；右键轻点=编辑注释。")
        return "break"

    def on_right_drag(self, event):
        if self.right_source_id is None or self.right_source_id not in self.nodes or self.right_start is None:
            return "break"
        x, y = self.cx(event), self.cy(event)
        sx0, sy0 = self.right_start
        if not self.right_dragging:
            if math.hypot(x - sx0, y - sy0) < self.DRAG_START_PX:
                return "break"
            self.right_dragging = True
            sx, sy = self.node_center(self.right_source_id)
            self.temp_line_id = self.canvas.create_line(
                sx, sy, x, y,
                fill=self.EDGE_COLORS[0],
                width=self.EDGE_WIDTH,
                arrow=tk.LAST,
                arrowshape=(10, 12, 4),
                dash=self.EDGE_DASH,
                tags=("temp_line",),
            )
            self.status.config(text="正在连线：拖到目标气泡后松开。")
        if self.temp_line_id is not None:
            sx, sy = self.node_center(self.right_source_id)
            self.canvas.coords(self.temp_line_id, sx, sy, x, y)
        return "break"

    def on_right_up(self, event):
        if self.right_source_id is None:
            return "break"
        x, y = self.cx(event), self.cy(event)
        source_id = self.right_source_id
        was_dragging = self.right_dragging
        if was_dragging:
            kind, data = self.get_top_item_data(x, y)
            if kind == "node" and data != source_id:
                self.record_undo()
                self.create_edge(source_id, data)
        if self.temp_line_id is not None:
            self.canvas.delete(self.temp_line_id)
        self.temp_line_id = None
        self.right_source_id = None
        self.right_start = None
        self.right_dragging = False

        # 右键轻点：编辑注释。右键拖动超过阈值：建立关联线。二者互不抢事件。
        if not was_dragging and source_id in self.nodes:
            self.open_note_editor(source_id)
        return "break"

    def on_right_double(self, event):
        # 右键单击已经用于打开注释；双击不再承担额外含义，避免重复触发。
        if self.temp_line_id is not None:
            self.canvas.delete(self.temp_line_id)
            self.temp_line_id = None
        self.right_source_id = None
        self.right_start = None
        self.right_dragging = False
        return "break"

    def node_center(self, nid):
        n = self.nodes[nid]
        return n["x"] + n["w"] / 2, n["y"] + n["h"] / 2

    # ---------- 快速新建：Tab / Enter ----------
    def on_tab_key(self, event=None):
        if self.entry is not None:
            return None
        if self.selected_kind == "node" and self.selected_id in self.nodes:
            self.spawn_from_node(self.selected_id, "right")
            return "break"
        return None

    def on_return_key(self, event=None):
        if self.entry is not None:
            return None
        if self.selected_kind == "node" and self.selected_id in self.nodes:
            self.spawn_from_node(self.selected_id, "down")
            return "break"
        return None

    def spawn_from_edit(self, direction):
        nid = self.edit_node_id
        if nid not in self.nodes:
            return "break"
        self.commit_edit_if_active()
        if nid in self.nodes:
            self.spawn_from_node(nid, direction)
        return "break"

    def spawn_from_node(self, nid, direction):
        if nid not in self.nodes:
            return None
        n = self.nodes[nid]
        if direction == "right":
            x = n["x"] + n["w"] + 10
            y = n["y"]
        else:
            x = n["x"]
            y = n["y"] + n["h"] + 10
        self.record_undo()
        new_id = self.create_node(x, y, "")
        self.start_edit_node(new_id, select_all=True)
        return new_id

    # ---------- 重连线端点 ----------
    def show_edge_handles_if_needed(self):
        self.clear_handles()
        if self.selected_kind != "edge" or self.selected_id not in self.edges:
            return
        eid = self.selected_id
        edge = self.edges[eid]
        if edge["source"] not in self.nodes or edge["target"] not in self.nodes:
            return
        x1, y1, x2, y2 = self.edge_display_points(eid)
        self.create_handle(eid, "source", x1, y1)
        self.create_handle(eid, "target", x2, y2)
        self.raise_handles()

    def create_handle(self, eid, endpoint, x, y):
        r = self.HANDLE_R
        item = self.canvas.create_oval(
            x - r, y - r, x + r, y + r,
            fill=self.EDGE_SELECTED,
            outline="#ffffff",
            width=1,
            tags=("handle", f"handle:{eid}:{endpoint}"),
        )
        self.handle_items.append(item)

    def clear_handles(self):
        for item in self.handle_items:
            try:
                self.canvas.delete(item)
            except tk.TclError:
                pass
        self.handle_items = []

    def raise_handles(self):
        for item in self.handle_items:
            self.canvas.tag_raise(item)

    def start_rewire(self, eid, endpoint, x, y):
        if eid not in self.edges:
            return
        edge = self.edges[eid]
        self.mode = "rewire"
        self.rewire = {"eid": eid, "endpoint": endpoint, "old_source": edge["source"], "old_target": edge["target"]}
        if self.temp_line_id is not None:
            self.canvas.delete(self.temp_line_id)
        if endpoint == "source":
            tx, ty = self.node_center(edge["target"])
            coords = (x, y, tx, ty)
        else:
            sx, sy = self.node_center(edge["source"])
            coords = (sx, sy, x, y)
        self.temp_line_id = self.canvas.create_line(
            *coords,
            fill=self.EDGE_COLORS[0],
            width=self.EDGE_WIDTH,
            arrow=tk.LAST,
            arrowshape=(10, 12, 4),
            dash=self.EDGE_DASH,
            tags=("temp_line",),
        )
        self.clear_handles()

    def update_rewire_temp(self, x, y):
        if not self.rewire or self.temp_line_id is None:
            return
        edge = self.edges[self.rewire["eid"]]
        if self.rewire["endpoint"] == "source":
            tx, ty = self.node_center(edge["target"])
            self.canvas.coords(self.temp_line_id, x, y, tx, ty)
        else:
            sx, sy = self.node_center(edge["source"])
            self.canvas.coords(self.temp_line_id, sx, sy, x, y)

    def finish_rewire(self, x, y):
        if not self.rewire:
            return
        eid = self.rewire["eid"]
        endpoint = self.rewire["endpoint"]
        kind, data = self.get_top_item_data(x, y)
        changed = False
        if eid in self.edges and kind == "node":
            edge = self.edges[eid]
            if endpoint == "source" and data != edge["target"] and data != edge["source"]:
                self.record_undo()
                edge["source"] = data
                changed = True
            elif endpoint == "target" and data != edge["source"] and data != edge["target"]:
                self.record_undo()
                edge["target"] = data
                changed = True
        if self.temp_line_id is not None:
            self.canvas.delete(self.temp_line_id)
            self.temp_line_id = None
        self.rewire = None
        self.recompute_depths()
        if eid in self.edges:
            self.select("edge", eid)

    # ---------- 文本编辑 ----------
    def start_edit_node(self, nid, select_all=False):
        if nid not in self.nodes:
            return
        self.close_note_editor(save=True)
        self.commit_edit_if_active()
        self.select("node", nid)
        self.edit_node_id = nid
        self.edit_original_text = self.nodes[nid].get("text", "")
        self.edit_undo_snapshot = self.current_data_snapshot()
        node = self.nodes[nid]

        self.entry = tk.Entry(self.canvas, font=self.font, relief=tk.FLAT, justify=tk.LEFT)
        self.entry.insert(0, node.get("text", ""))
        if select_all:
            self.entry.selection_range(0, tk.END)
        self.entry_window = self.canvas.create_window(
            node["x"] + self.NODE_PAD_X * 0.65,
            node["y"] + max(3, (node["h"] - 20) / 2),
            anchor="nw",
            window=self.entry,
            width=max(40, node["w"] - self.NODE_PAD_X * 1.3),
            height=20,
        )
        self.entry.focus_set()
        self.entry.bind("<Tab>", lambda e: self.spawn_from_edit("right"))
        self.entry.bind("<Return>", lambda e: self.spawn_from_edit("down"))
        self.entry.bind("<KP_Enter>", lambda e: self.spawn_from_edit("down"))
        self.entry.bind("<Escape>", lambda e: self.cancel_edit())
        self.entry.bind("<Control-z>", self.undo_last)
        self.entry.bind("<Control-Z>", self.undo_last)
        self.entry.bind("<FocusOut>", lambda e: self.commit_edit_if_active())
        self.entry.bind("<KeyRelease>", self.live_resize_editing_node)
        self.status.config(text="正在输入：Tab 在右侧10px生成新气泡；Enter 在下方10px生成新气泡；Esc 撤销；空内容会自动删除。")

    def live_resize_editing_node(self, event=None):
        if self.entry is None or self.edit_node_id not in self.nodes:
            return
        if event is not None and event.keysym in {"Tab", "Return", "KP_Enter", "Escape"}:
            return
        nid = self.edit_node_id
        self.nodes[nid]["text"] = self.entry.get()
        # 关键：node['x'] 不变，所以文字增长只会把气泡向右侧推开。
        self.redraw_node(nid)
        self.redraw_edges_for_node(nid)
        node = self.nodes[nid]
        if self.entry_window is not None:
            self.canvas.coords(self.entry_window, node["x"] + self.NODE_PAD_X * 0.65, node["y"] + max(3, (node["h"] - 20) / 2))
            self.canvas.itemconfigure(self.entry_window, width=max(40, node["w"] - self.NODE_PAD_X * 1.3), height=20)
            self.canvas.tag_raise(self.entry_window)

    def commit_edit_if_active(self):
        if self.entry is None:
            return
        nid = self.edit_node_id
        text = self.entry.get()
        original_text = self.edit_original_text
        undo_snapshot = self.edit_undo_snapshot
        if nid in self.nodes and text != original_text:
            self.record_undo_snapshot(undo_snapshot)
            self.nodes[nid]["text"] = text

        entry = self.entry
        window = self.entry_window
        self.entry = None
        self.entry_window = None
        self.edit_node_id = None
        self.edit_undo_snapshot = None
        try:
            entry.destroy()
        except tk.TclError:
            pass
        if window is not None:
            self.canvas.delete(window)

        if nid in self.nodes and not text.strip():
            self.delete_node(nid)
            if self.selected_kind == "node" and self.selected_id == nid:
                self.selected_kind, self.selected_id = None, None
            self.recompute_depths()
            self.status.config(text="空内容气泡已自动删除。")
            return
        if nid in self.nodes:
            self.redraw_node(nid)
            self.redraw_edges_for_node(nid)
        self.status.config(text="输入完成。Tab/Enter 可继续快速生成气泡；右键拖气泡可连虚线箭头。")

    def cancel_edit(self):
        if self.entry is None:
            return "break"
        nid = self.edit_node_id
        if nid in self.nodes:
            self.nodes[nid]["text"] = self.edit_original_text
        entry = self.entry
        window = self.entry_window
        self.entry = None
        self.entry_window = None
        self.edit_node_id = None
        self.edit_undo_snapshot = None
        try:
            entry.destroy()
        except tk.TclError:
            pass
        if window is not None:
            self.canvas.delete(window)
        if nid in self.nodes and not self.nodes[nid].get("text", "").strip():
            self.delete_node(nid)
            if self.selected_kind == "node" and self.selected_id == nid:
                self.selected_kind, self.selected_id = None, None
            self.recompute_depths()
            self.status.config(text="空内容气泡已自动删除。")
            return "break"
        if nid in self.nodes:
            self.redraw_node(nid)
            self.redraw_edges_for_node(nid)
        self.status.config(text="已撤销本次输入。")
        return "break"

    # ---------- 注释：右键轻点编辑 / 悬停显示 / 斜线追踪 ----------
    def open_note_editor(self, nid):
        if nid not in self.nodes:
            return
        self.commit_edit_if_active()
        self.hide_note_popup()
        self.close_note_editor(save=True)
        self.select("node", nid)
        self.note_editor_undo_snapshot = self.current_data_snapshot()

        node = self.nodes[nid]
        w = max(self.NOTE_MIN_W, float(node.get("note_w", self.NOTE_EDITOR_W) or self.NOTE_EDITOR_W))
        h = max(self.NOTE_MIN_H, float(node.get("note_h", self.NOTE_EDITOR_H) or self.NOTE_EDITOR_H))
        x, y = self.default_note_box_position(nid, w, h)

        line = self.canvas.create_line(0, 0, 0, 0, fill=self.NOTE_LINE, width=1.5, dash=(3, 3), tags=("note_editor",))
        frame = tk.Frame(self.canvas, bg=self.NOTE_BORDER, bd=0, highlightthickness=0)
        text_box = tk.Text(frame, wrap=tk.WORD, font=self.font, relief=tk.FLAT, undo=True, padx=8, pady=6)
        text_box.pack(fill=tk.BOTH, expand=True, padx=2, pady=2)
        text_box.insert("1.0", node.get("note", ""))
        window = self.canvas.create_window(x, y, anchor="nw", window=frame, width=w, height=h, tags=("note_editor",))

        right_handle = self.canvas.create_rectangle(0, 0, 0, 0, outline="", fill="", tags=("note_editor", "note_editor_handle"))
        bottom_handle = self.canvas.create_rectangle(0, 0, 0, 0, outline="", fill="", tags=("note_editor", "note_editor_handle"))
        corner_handle = self.canvas.create_rectangle(0, 0, 0, 0, outline="#777777", fill="#dddddd", tags=("note_editor", "note_editor_handle"))

        self.note_editor = {
            "nid": nid,
            "x": x,
            "y": y,
            "w": w,
            "h": h,
            "line": line,
            "frame": frame,
            "text": text_box,
            "window": window,
            "right_handle": right_handle,
            "bottom_handle": bottom_handle,
            "corner_handle": corner_handle,
            "resize_zone": None,
            "resize_start": None,
            "resize_original": None,
        }
        text_box.focus_set()
        text_box.bind("<Escape>", lambda e: self.close_note_editor(save=True))
        text_box.bind("<Control-z>", self.undo_last)
        text_box.bind("<Control-Z>", self.undo_last)
        self.update_note_editor_geometry()
        self.status.config(text="正在编辑注释：可拖动右边/下边/右下角改变大小；点击注释框外任意位置会保存并关闭。")
        return "break"

    def default_note_box_position(self, nid, w, h):
        """优先把注释框放在视野内且不压住其他气泡的最近空位。"""
        if nid not in self.nodes:
            return self.canvas.canvasx(40), self.canvas.canvasy(40)
        node = self.nodes[nid]
        view_x0 = self.canvas.canvasx(0)
        view_y0 = self.canvas.canvasy(0)
        view_x1 = self.canvas.canvasx(max(1, self.canvas.winfo_width()))
        view_y1 = self.canvas.canvasy(max(1, self.canvas.winfo_height()))
        margin = 12
        gap = 36
        cx = node["x"] + node["w"] / 2
        cy = node["y"] + node["h"] / 2

        candidates = [
            (node["x"] + node["w"] + gap, node["y"] - 8),                 # 右侧，最常用
            (node["x"] - w - gap, node["y"] - 8),                           # 左侧
            (cx - w / 2, node["y"] + node["h"] + gap),                     # 下方
            (cx - w / 2, node["y"] - h - gap),                              # 上方
            (node["x"] + node["w"] + gap, node["y"] + node["h"] + gap), # 右下
            (node["x"] + node["w"] + gap, node["y"] - h - gap),          # 右上
            (node["x"] - w - gap, node["y"] + node["h"] + gap),          # 左下
            (node["x"] - w - gap, node["y"] - h - gap),                   # 左上
        ]

        best = None
        best_score = None
        for x, y in candidates:
            x = min(max(x, view_x0 + margin), view_x1 - w - margin)
            y = min(max(y, view_y0 + margin), view_y1 - h - margin)
            rect = (x, y, x + w, y + h)
            overlap_area = self.note_box_overlap_area(rect, ignore_nid=nid)
            distance = math.hypot((x + w / 2) - cx, (y + h / 2) - cy)
            # 先强烈惩罚压住气泡，再按距离选最近空位。
            score = overlap_area * 1000 + distance
            if best is None or score < best_score:
                best = (x, y)
                best_score = score
                if overlap_area == 0:
                    # 候选顺序已经按常用/视觉追踪友好排序；找到第一处空位就用。
                    break
        return best if best else (node["x"] + node["w"] + gap, node["y"])

    def note_box_overlap_area(self, rect, ignore_nid=None):
        total = 0.0
        x1, y1, x2, y2 = rect
        pad = 8
        for nid, node in self.nodes.items():
            if nid == ignore_nid:
                continue
            nx1 = node["x"] - pad
            ny1 = node["y"] - pad
            nx2 = node["x"] + node["w"] + pad
            ny2 = node["y"] + node["h"] + pad
            ix = max(0.0, min(x2, nx2) - max(x1, nx1))
            iy = max(0.0, min(y2, ny2) - max(y1, ny1))
            total += ix * iy
        return total

    def widget_is_inside_note_editor(self, widget):
        if self.note_editor is None:
            return False
        frame = self.note_editor.get("frame")
        text = self.note_editor.get("text")
        w = widget
        while w is not None:
            if w is frame or w is text:
                return True
            try:
                w = w.master
            except Exception:
                return False
        return False

    def on_global_left_click(self, event):
        if self.note_editor is None:
            return None
        if self.widget_is_inside_note_editor(event.widget):
            return None
        # 画板内点击由 on_left_down 处理；这里主要兜底处理工具栏/窗口其他区域。
        if event.widget is not self.canvas:
            self.close_note_editor(save=True)
        return None

    def on_global_right_click(self, event):
        if self.note_editor is None:
            return None
        if self.widget_is_inside_note_editor(event.widget):
            return None
        # 画板内右键由 on_right_down 处理；这里主要兜底处理工具栏/窗口其他区域。
        if event.widget is not self.canvas:
            self.close_note_editor(save=True)
        return None

    def note_connection_points(self, nid, bx, by, bw, bh):
        node = self.nodes[nid]
        ncx = node["x"] + node["w"] / 2
        ncy = node["y"] + node["h"] / 2
        bcx = bx + bw / 2
        if bcx >= ncx:
            sx = node["x"] + node["w"]
            sy = ncy
            tx = bx
            ty = by + min(max(18, bh * 0.28), bh - 12)
        else:
            sx = node["x"]
            sy = ncy
            tx = bx + bw
            ty = by + min(max(18, bh * 0.28), bh - 12)
        return sx, sy, tx, ty

    def update_note_editor_geometry(self):
        ed = self.note_editor
        if not ed or ed["nid"] not in self.nodes:
            return
        x, y, w, h = ed["x"], ed["y"], ed["w"], ed["h"]
        sx, sy, tx, ty = self.note_connection_points(ed["nid"], x, y, w, h)
        self.canvas.coords(ed["line"], sx, sy, tx, ty)
        self.canvas.coords(ed["window"], x, y)
        self.canvas.itemconfigure(ed["window"], width=w, height=h)
        hit = self.NOTE_RESIZE_HIT
        self.canvas.coords(ed["right_handle"], x + w - hit, y, x + w + hit, y + h)
        self.canvas.coords(ed["bottom_handle"], x, y + h - hit, x + w, y + h + hit)
        self.canvas.coords(ed["corner_handle"], x + w - 10, y + h - 10, x + w + 2, y + h + 2)
        for key in ("line", "window", "right_handle", "bottom_handle", "corner_handle"):
            self.canvas.tag_raise(ed[key])

    def note_editor_zone(self, x, y):
        ed = self.note_editor
        if not ed:
            return None
        bx, by, bw, bh = ed["x"], ed["y"], ed["w"], ed["h"]
        hit = self.NOTE_RESIZE_HIT
        if bx + bw - hit <= x <= bx + bw + hit and by + bh - hit <= y <= by + bh + hit:
            return "corner"
        if bx + bw - hit <= x <= bx + bw + hit and by <= y <= by + bh:
            return "right"
        if bx <= x <= bx + bw and by + bh - hit <= y <= by + bh + hit:
            return "bottom"
        if bx <= x <= bx + bw and by <= y <= by + bh:
            return "inside"
        return None

    def start_note_resize(self, zone, x, y):
        ed = self.note_editor
        if not ed:
            return
        self.mode = "note_resize"
        ed["resize_zone"] = zone
        ed["resize_start"] = (x, y)
        ed["resize_original"] = (ed["w"], ed["h"])
        self.status.config(text="正在调整注释框大小。")

    def update_note_resize(self, x, y):
        ed = self.note_editor
        if not ed or not ed.get("resize_start") or not ed.get("resize_original"):
            return
        sx, sy = ed["resize_start"]
        ow, oh = ed["resize_original"]
        zone = ed.get("resize_zone")
        if zone in {"right", "corner"}:
            ed["w"] = max(self.NOTE_MIN_W, ow + (x - sx))
        if zone in {"bottom", "corner"}:
            ed["h"] = max(self.NOTE_MIN_H, oh + (y - sy))
        self.update_note_editor_geometry()

    def finish_note_resize(self):
        ed = self.note_editor
        if not ed:
            return
        nid = ed.get("nid")
        if nid in self.nodes:
            self.nodes[nid]["note_w"] = ed["w"]
            self.nodes[nid]["note_h"] = ed["h"]
        ed["resize_zone"] = None
        ed["resize_start"] = None
        ed["resize_original"] = None
        self.status.config(text="注释框大小已调整。点击框外会保存并关闭。")

    def close_note_editor(self, save=True):
        ed = self.note_editor
        if not ed:
            return None
        nid = ed.get("nid")
        old_snapshot = self.note_editor_undo_snapshot
        new_note = ""
        if ed.get("text") is not None:
            try:
                new_note = ed["text"].get("1.0", "end-1c")
            except tk.TclError:
                new_note = ""
        old_note = self.nodes.get(nid, {}).get("note", "") if nid in self.nodes else ""
        old_w = self.nodes.get(nid, {}).get("note_w", self.NOTE_EDITOR_W) if nid in self.nodes else self.NOTE_EDITOR_W
        old_h = self.nodes.get(nid, {}).get("note_h", self.NOTE_EDITOR_H) if nid in self.nodes else self.NOTE_EDITOR_H
        if save and nid in self.nodes:
            if new_note != old_note or abs(float(ed["w"]) - float(old_w)) > 0.1 or abs(float(ed["h"]) - float(old_h)) > 0.1:
                self.record_undo_snapshot(old_snapshot)
            self.nodes[nid]["note"] = new_note
            self.nodes[nid]["note_w"] = ed["w"]
            self.nodes[nid]["note_h"] = ed["h"]
        for key in ("line", "window", "right_handle", "bottom_handle", "corner_handle"):
            item = ed.get(key)
            if item is not None:
                try:
                    self.canvas.delete(item)
                except tk.TclError:
                    pass
        frame = ed.get("frame")
        if frame is not None:
            try:
                frame.destroy()
            except tk.TclError:
                pass
        self.note_editor = None
        self.note_editor_undo_snapshot = None
        if nid in self.nodes:
            self.redraw_node(nid)
            self.status.config(text="注释已保存。右键轻点可再次编辑；鼠标悬停气泡可显示注释。")
        return "break"

    def destroy_note_editor_without_commit(self):
        ed = self.note_editor
        if not ed:
            return
        for key in ("line", "window", "right_handle", "bottom_handle", "corner_handle"):
            item = ed.get(key)
            if item is not None:
                try:
                    self.canvas.delete(item)
                except tk.TclError:
                    pass
        frame = ed.get("frame")
        if frame is not None:
            try:
                frame.destroy()
            except tk.TclError:
                pass
        self.note_editor = None
        self.note_editor_undo_snapshot = None

    def on_canvas_motion(self, event):
        if self.note_editor is not None:
            return
        x, y = self.cx(event), self.cy(event)
        nid = self.node_at(x, y)
        self.hover_node_id = nid
        if nid is None or nid not in self.nodes:
            self.hide_note_popup()
            return
        note = str(self.nodes[nid].get("note", "")).strip()
        if not note:
            self.hide_note_popup()
            return
        if self.note_popup_node_id == nid and self.note_popup_items:
            return
        self.show_note_popup(nid, note)

    def show_note_popup(self, nid, note):
        self.hide_note_popup()
        if nid not in self.nodes:
            return
        node = self.nodes[nid]
        w = max(220, min(420, float(node.get("note_w", self.NOTE_EDITOR_W) or self.NOTE_EDITOR_W)))
        # 先临时测高，再用最终高度重新找最近空位，避免悬浮注释压住附近气泡。
        tmp_x, tmp_y = self.default_note_box_position(nid, w, 90)
        text = self.canvas.create_text(
            tmp_x + 8, tmp_y + 8,
            anchor="nw",
            text=note,
            fill="#111111",
            font=self.small_font,
            width=w - 16,
            justify=tk.LEFT,
            tags=("note_popup",),
        )
        bbox = self.canvas.bbox(text) or (tmp_x, tmp_y, tmp_x + w, tmp_y + 80)
        h = max(42, (bbox[3] - bbox[1]) + 16)
        x, y = self.default_note_box_position(nid, w, h)
        self.canvas.coords(text, x + 8, y + 8)
        sx, sy, tx, ty = self.note_connection_points(nid, x, y, w, h)
        line = self.canvas.create_line(sx, sy, tx, ty, fill=self.NOTE_LINE, width=1.2, dash=(3, 3), tags=("note_popup",))
        rect = self.canvas.create_rectangle(x, y, x + w, y + h, fill=self.NOTE_BG, outline=self.NOTE_BORDER, width=2, tags=("note_popup",))
        self.canvas.tag_raise(line)
        self.canvas.tag_raise(rect)
        self.canvas.tag_raise(text)
        self.note_popup_items = [line, rect, text]
        self.note_popup_node_id = nid

    def hide_note_popup(self):
        for item in self.note_popup_items:
            try:
                self.canvas.delete(item)
            except tk.TclError:
                pass
        self.note_popup_items = []
        self.note_popup_node_id = None

    # ---------- 删除/取消 ----------
    def delete_selected(self, event=None):
        if self.entry is not None and self.entry.focus_get() == self.entry:
            return
        ids = self.get_selected_node_ids()
        if ids:
            self.record_undo()
            for nid in list(ids):
                self.delete_node(nid)
        elif self.selected_kind == "edge" and self.selected_id in self.edges:
            self.record_undo()
            self.delete_edge(self.selected_id)
        self.clear_selection()
        self.recompute_depths()
        return "break"

    def delete_node(self, nid):
        if nid not in self.nodes:
            return
        for eid in [eid for eid, e in self.edges.items() if e["source"] == nid or e["target"] == nid]:
            self.delete_edge(eid, recompute=False)
        node = self.nodes.pop(nid)
        for key in ("body", "text_item", "note_item"):
            item = node.get(key)
            if item:
                self.canvas.delete(item)
        self.depths.pop(nid, None)
        if self.hover_node_id == nid:
            self.hide_note_popup()
        if self.note_editor is not None and self.note_editor.get("nid") == nid:
            self.destroy_note_editor_without_commit()

    def delete_edge(self, eid, recompute=True):
        if eid not in self.edges:
            return
        edge = self.edges.pop(eid)
        for key in ("hit", "line"):
            item = edge.get(key)
            if item:
                self.canvas.delete(item)
        if recompute:
            self.recompute_depths()
            self.redraw_all_edges()

    def cancel_current_action(self, event=None):
        if self.note_editor is not None:
            return self.close_note_editor(save=True)
        if self.entry is not None:
            return self.cancel_edit()
        if self.temp_line_id is not None:
            self.canvas.delete(self.temp_line_id)
            self.temp_line_id = None
        if self.selection_rect is not None:
            self.canvas.delete(self.selection_rect)
            self.selection_rect = None
        self.clear_snap_guides()
        self.rewire = None
        self.right_source_id = None
        self.right_start = None
        self.right_dragging = False
        self.lasso_start = None
        self.mode = None
        self.show_edge_handles_if_needed()
        self.status.config(text="已取消当前操作。")
        return "break"

    # ---------- 撤销：最多记忆最近 3 个操作 ----------
    def record_undo(self):
        if self.is_restoring_undo:
            return
        self.record_undo_snapshot(self.current_data_snapshot())

    def record_undo_snapshot(self, data):
        if self.is_restoring_undo or data is None:
            return
        key = json.dumps(data, ensure_ascii=False, sort_keys=True)
        if self.undo_stack:
            last_key = json.dumps(self.undo_stack[-1], ensure_ascii=False, sort_keys=True)
            if key == last_key:
                return
        self.undo_stack.append(json.loads(json.dumps(data, ensure_ascii=False)))
        if len(self.undo_stack) > 3:
            self.undo_stack = self.undo_stack[-3:]

    def undo_last(self, event=None):
        # 正在编辑时，Ctrl+Z 优先回到进入编辑前的状态，不需要先提交。
        if self.entry is not None and self.edit_undo_snapshot is not None:
            current_text = self.entry.get()
            if current_text != self.edit_original_text:
                target_key = json.dumps(self.edit_undo_snapshot, ensure_ascii=False, sort_keys=True)
                if self.undo_stack:
                    last_key = json.dumps(self.undo_stack[-1], ensure_ascii=False, sort_keys=True)
                    if last_key == target_key:
                        self.undo_stack.pop()
                self.apply_data_snapshot(self.edit_undo_snapshot)
                self.status.config(text="已撤销当前编辑。")
                return "break"

        if self.note_editor is not None and self.note_editor_undo_snapshot is not None:
            ed = self.note_editor
            nid = ed.get("nid")
            current_note = ""
            try:
                current_note = ed["text"].get("1.0", "end-1c")
            except tk.TclError:
                current_note = ""
            old_note = self.nodes.get(nid, {}).get("note", "") if nid in self.nodes else ""
            if current_note != old_note:
                target_key = json.dumps(self.note_editor_undo_snapshot, ensure_ascii=False, sort_keys=True)
                if self.undo_stack:
                    last_key = json.dumps(self.undo_stack[-1], ensure_ascii=False, sort_keys=True)
                    if last_key == target_key:
                        self.undo_stack.pop()
                self.apply_data_snapshot(self.note_editor_undo_snapshot)
                self.status.config(text="已撤销当前注释编辑。")
                return "break"

        if not self.undo_stack:
            self.status.config(text="没有可撤销的操作。只记忆最近 3 个操作。")
            return "break"
        snapshot = self.undo_stack.pop()
        self.apply_data_snapshot(snapshot)
        self.status.config(text=f"已撤销上一个操作。还可撤销 {len(self.undo_stack)} 步。")
        return "break"

    def destroy_entry_without_commit(self):
        if self.entry is not None:
            try:
                self.entry.destroy()
            except tk.TclError:
                pass
        if self.entry_window is not None:
            try:
                self.canvas.delete(self.entry_window)
            except tk.TclError:
                pass
        self.entry = None
        self.entry_window = None
        self.edit_node_id = None
        self.edit_original_text = ""
        self.edit_undo_snapshot = None

    def apply_data_snapshot(self, data):
        self.is_restoring_undo = True
        try:
            self.destroy_entry_without_commit()
            self.destroy_note_editor_without_commit()
            self.hide_note_popup()
            if self.temp_line_id is not None:
                try:
                    self.canvas.delete(self.temp_line_id)
                except tk.TclError:
                    pass
            self.temp_line_id = None
            self.right_source_id = None
            self.right_start = None
            self.right_dragging = False
            self.rewire = None
            self.mode = None
            self.drag_node_id = None
            self.drag_group_ids = []
            self.drag_group_anchor_id = None
            self.drag_group_original = {}
            self.drag_start_canvas = None
            self.lasso_start = None
            self.selection_rect = None
            self.snap_guides = []
            self.drag_undo_recorded = False

            self.canvas.delete("all")
            self.nodes.clear()
            self.edges.clear()
            self.depths.clear()
            self.handle_items.clear()
            self.selected_kind = None
            self.selected_id = None
            self.selected_ids = set()

            version = int(data.get("version", 0) or 0)
            coordinates = data.get("coordinates", "center" if version < 4 else "left_top")
            max_nid = 0
            max_eid = 0

            for item in data.get("nodes", []):
                text = item.get("text", "")
                if not str(text).strip():
                    continue
                nid = int(item["id"])
                max_nid = max(max_nid, nid)
                note = item.get("note", "")
                x = float(item.get("x", 0))
                y = float(item.get("y", 0))
                _, w, h = self.measure_node(text)
                if coordinates != "left_top":
                    x -= w / 2
                    y -= h / 2
                self.nodes[nid] = {
                    "id": nid,
                    "x": x,
                    "y": y,
                    "text": text,
                    "note": note,
                    "note_w": float(item.get("note_w", self.NOTE_EDITOR_W) or self.NOTE_EDITOR_W),
                    "note_h": float(item.get("note_h", self.NOTE_EDITOR_H) or self.NOTE_EDITOR_H),
                    "w": w,
                    "h": h,
                    "body": None,
                    "text_item": None,
                    "note_item": None,
                }

            for item in data.get("edges", []):
                eid = int(item["id"])
                s = int(item["source"])
                t = int(item["target"])
                if s in self.nodes and t in self.nodes and s != t:
                    max_eid = max(max_eid, eid)
                    self.edges[eid] = {"id": eid, "source": s, "target": t, "hit": None, "line": None}

            self.next_node_id = max_nid + 1
            self.next_edge_id = max_eid + 1
            self.recompute_depths()
            self.clear_selection()
        finally:
            self.is_restoring_undo = False

    # ---------- 保存 / 加载 / 自动缓存 ----------
    def current_data_snapshot(self):
        active_text = None
        active_nid = self.edit_node_id if self.entry is not None else None
        if self.entry is not None and active_nid in self.nodes:
            active_text = self.entry.get()

        active_note_nid = None
        active_note = None
        active_note_w = None
        active_note_h = None
        if self.note_editor is not None:
            active_note_nid = self.note_editor.get("nid")
            if active_note_nid in self.nodes:
                try:
                    active_note = self.note_editor["text"].get("1.0", "end-1c")
                except tk.TclError:
                    active_note = self.nodes[active_note_nid].get("note", "")
                active_note_w = self.note_editor.get("w", self.NOTE_EDITOR_W)
                active_note_h = self.note_editor.get("h", self.NOTE_EDITOR_H)

        valid_nodes = set()
        nodes_data = []
        for nid, n in self.nodes.items():
            text = active_text if nid == active_nid else n.get("text", "")
            if not str(text).strip():
                continue
            valid_nodes.add(nid)
            note = active_note if nid == active_note_nid else n.get("note", "")
            note_w = active_note_w if nid == active_note_nid else n.get("note_w", self.NOTE_EDITOR_W)
            note_h = active_note_h if nid == active_note_nid else n.get("note_h", self.NOTE_EDITOR_H)
            nodes_data.append({
                "id": nid,
                "x": n["x"],
                "y": n["y"],
                "w": n.get("w", self.NODE_MIN_W),
                "h": n.get("h", self.NODE_MIN_H),
                "text": text,
                "note": note,
                "note_w": note_w,
                "note_h": note_h,
            })

        edges_data = []
        for eid, e in self.edges.items():
            if e["source"] in valid_nodes and e["target"] in valid_nodes and e["source"] != e["target"]:
                edges_data.append({"id": eid, "source": e["source"], "target": e["target"]})

        return {
            "version": 7,
            "coordinates": "left_top",
            "nodes": nodes_data,
            "edges": edges_data,
        }

    def atomic_write_json(self, path, data):
        directory = os.path.dirname(path) or "."
        os.makedirs(directory, exist_ok=True)
        fd, tmp_path = tempfile.mkstemp(prefix=".workflow.", suffix=".tmp", dir=directory, text=True)
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
                f.write("\n")
            os.replace(tmp_path, path)
        finally:
            if os.path.exists(tmp_path):
                try:
                    os.remove(tmp_path)
                except OSError:
                    pass

    def write_flow_to_path(self, path, silent=False):
        data = self.current_data_snapshot()
        self.atomic_write_json(path, data)
        if not silent:
            self.status.config(text=f"已保存：{path}")

    def save_flow(self, save_as=False):
        self.commit_edit_if_active()
        if save_as:
            path = filedialog.asksaveasfilename(
                defaultextension=".json",
                filetypes=[("JSON flow", "*.json"), ("All files", "*.*")],
            )
            if not path:
                return
            self.file_path = path
        elif not self.file_path:
            self.file_path = self.autosave_path
        self.write_flow_to_path(self.file_path, silent=False)

    def autosave_flow(self):
        try:
            self.write_flow_to_path(self.autosave_path, silent=True)
            self.status.config(text=f"已自动缓存到：{self.autosave_path}")
        except Exception as exc:
            self.status.config(text=f"自动缓存失败：{exc}")
        finally:
            self.schedule_autosave()

    def schedule_autosave(self):
        if self.autosave_job is not None:
            try:
                self.root.after_cancel(self.autosave_job)
            except tk.TclError:
                pass
        self.autosave_job = self.root.after(self.AUTOSAVE_MS, self.autosave_flow)

    def load_flow(self):
        self.commit_edit_if_active()
        path = filedialog.askopenfilename(filetypes=[("JSON flow", "*.json"), ("All files", "*.*")])
        if not path:
            return
        self.record_undo()
        self.load_flow_from_path(path, set_as_file=True, silent=False)

    def load_default_workflow_if_exists(self):
        if not os.path.exists(self.autosave_path):
            self.status.config(text=f"默认缓存文件：{self.autosave_path}。每分钟自动缓存，启动自动读取。")
            return
        try:
            self.load_flow_from_path(self.autosave_path, set_as_file=True, silent=True)
            self.status.config(text=f"已自动加载默认 workflow：{self.autosave_path}。每分钟自动缓存。")
        except Exception as exc:
            self.status.config(text=f"默认 workflow.json 加载失败：{exc}。会在下次自动缓存时重建。")

    def load_flow_from_path(self, path, set_as_file=True, silent=False):
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        self.clear_all(no_confirm=True, preserve_file_path=True)

        version = int(data.get("version", 0) or 0)
        coordinates = data.get("coordinates", "center" if version < 4 else "left_top")
        max_nid = 0
        max_eid = 0

        # 先建节点；老版本 workflow 没有 version，x/y 是中心点，这里自动迁移成左上角。
        for item in data.get("nodes", []):
            text = item.get("text", "")
            if not str(text).strip():
                continue
            nid = int(item["id"])
            max_nid = max(max_nid, nid)
            note = item.get("note", "")
            x = float(item.get("x", 0))
            y = float(item.get("y", 0))
            _, w, h = self.measure_node(text)
            if coordinates != "left_top":
                x -= w / 2
                y -= h / 2
            self.nodes[nid] = {
                "id": nid,
                "x": x,
                "y": y,
                "text": text,
                "note": note,
                "note_w": float(item.get("note_w", self.NOTE_EDITOR_W) or self.NOTE_EDITOR_W),
                "note_h": float(item.get("note_h", self.NOTE_EDITOR_H) or self.NOTE_EDITOR_H),
                "w": w,
                "h": h,
                "body": None,
                "text_item": None,
                "note_item": None,
            }

        for item in data.get("edges", []):
            eid = int(item["id"])
            s = int(item["source"])
            t = int(item["target"])
            if s in self.nodes and t in self.nodes and s != t:
                max_eid = max(max_eid, eid)
                self.edges[eid] = {"id": eid, "source": s, "target": t, "hit": None, "line": None}

        self.next_node_id = max_nid + 1
        self.next_edge_id = max_eid + 1
        if set_as_file:
            self.file_path = path
        self.recompute_depths()
        self.clear_selection()
        if not silent:
            self.status.config(text=f"已打开：{path}")

    def on_close(self):
        try:
            self.close_note_editor(save=True)
            self.write_flow_to_path(self.autosave_path, silent=True)
        except Exception:
            pass
        self.hide_note_popup()
        self.root.destroy()

    def clear_all_confirm(self):
        if messagebox.askyesno("清空", "确定清空当前画板？未保存内容会丢失。"):
            self.record_undo()
            self.clear_all(no_confirm=True)

    def clear_all(self, no_confirm=False, preserve_file_path=False):
        self.commit_edit_if_active()
        self.close_note_editor(save=True)
        self.hide_note_popup()
        self.clear_snap_guides()
        self.canvas.delete("all")
        self.nodes.clear()
        self.edges.clear()
        self.depths.clear()
        self.handle_items.clear()
        self.next_node_id = 1
        self.next_edge_id = 1
        self.selected_kind = None
        self.selected_id = None
        self.selected_ids = set()
        self.mode = None
        self.temp_line_id = None
        self.rewire = None
        self.right_source_id = None
        self.right_start = None
        self.right_dragging = False
        self.note_editor = None
        self.note_editor_undo_snapshot = None
        self.drag_node_id = None
        self.drag_group_ids = []
        self.drag_group_anchor_id = None
        self.drag_group_original = {}
        self.drag_start_canvas = None
        self.selection_rect = None
        self.lasso_start = None
        self.snap_guides = []
        if not preserve_file_path:
            self.file_path = self.autosave_path
        self.status.config(text="已清空。空白处左键新建气泡。Ctrl+Z 可撤销清空。")


def main():
    root = tk.Tk()
    CompactFlowCanvas(root)
    root.mainloop()


if __name__ == "__main__":
    main()
