-- Prove2me | Definitions.Def_CSL_Shared_Memory_TapeMachine
-- name    : CSL_Shared_Memory_TapeMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:20:43.408285+00:00
-- url     : https://prove2.me/theorems/5c2b7194-057b-4a49-8491-4c85d4eed225
-- title:
--   Coded sorting library: Shared / Memory / TapeMachine
-- statement:
--   Module `CodedSorting.Shared.Memory.TapeMachine` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # A concrete three-block cache for an adjacent-head tape
--
--   Unlike `BlockAccounting`, this file defines the cache contents, writeback,
--   reload, and execution.  The infinite function is the external disk, not RAM;
--   RAM holds exactly `3 * B` symbols and a fixed number of position counters.
--   The reconstructed tape `view` is a specification, never a stored array.
--
--   The simulator takes an adjacent-head tape program as input and bounds its
--   cache transfers in terms of that program's tape execution.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Memory.TapeMachine

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Memory_BlockAccounting
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# A concrete three-block cache for an adjacent-head tape

Unlike `BlockAccounting`, this file defines the cache contents, writeback,
reload, and execution.  The infinite function is the external disk, not RAM;
RAM holds exactly `3 * B` symbols and a fixed number of position counters.
The reconstructed tape `view` is a specification, never a stored array.

The simulator takes an adjacent-head tape program as input and bounds its
cache transfers in terms of that program's tape execution.
-/

namespace CSL.TapeMachine

variable {α : Type*} {B : ℕ}

abbrev Tape (α : Type*) := ℤ → α

/-- `origin` is the first address of the three-block buffer. -/
structure Cache (B : ℕ) (α : Type*) where
  origin : ℤ
  buffer : Fin (3 * B) → α
  disk : Tape α

def resident (c : Cache B α) (p : ℤ) : Prop :=
  c.origin ≤ p ∧ p < c.origin + 3 * (B : ℤ)

instance (c : Cache B α) (p : ℤ) : Decidable (resident c p) :=
  inferInstanceAs (Decidable (_ ∧ _))

def slot (c : Cache B α) (p : ℤ) (h : resident c p) : Fin (3 * B) :=
  ⟨(p - c.origin).toNat, by
    change c.origin ≤ p ∧ p < c.origin + 3 * (B : ℤ) at h
    omega⟩

theorem slot_address (c : Cache B α) (p : ℤ) (h : resident c p) :
    c.origin + (slot c p h : ℤ) = p := by
  have h0 : 0 ≤ p - c.origin := by rcases h with ⟨h, _⟩; omega
  simp only [slot, Int.toNat_of_nonneg h0]
  omega

/-- The logical tape is the dirty cache inside its window, disk elsewhere. -/
def view (c : Cache B α) : Tape α := fun p =>
  if h : resident c p then c.buffer (slot c p h) else c.disk p

/-- A three-block contiguous read, centered on the block containing `p`. -/
def load (disk : Tape α) (p : ℤ) (B : ℕ) : Cache B α where
  origin := (p / (B : ℤ) - 1) * (B : ℤ)
  buffer := fun i => disk ((p / (B : ℤ) - 1) * (B : ℤ) + (i : ℤ))
  disk := disk

theorem view_load (disk : Tape α) (p : ℤ) (B : ℕ) :
    view (load disk p B) = disk := by
  funext q
  try dsimp only [view]
  split_ifs with h
  · change disk ((load disk p B).origin + (slot (load disk p B) q h : ℤ)) = disk q
    rw [slot_address]
  · rfl

theorem load_middle (disk : Tape α) (p : ℤ) (hB : 0 < B) :
    (load disk p B).origin + (B : ℤ) ≤ p ∧
    p < (load disk p B).origin + 2 * (B : ℤ) := by
  have hb : 0 < (B : ℤ) := by exact_mod_cast hB
  have hlo := Int.emod_nonneg p (ne_of_gt hb)
  have hhi := Int.emod_lt_of_pos p hb
  have heq := Int.ediv_mul_add_emod p (B : ℤ)
  try dsimp only [load]
  constructor <;> nlinarith

theorem load_resident (disk : Tape α) (p : ℤ) (hB : 0 < B) :
    resident (load disk p B) p := by
  have h := load_middle disk p hB
  have hb : 0 < (B : ℤ) := by exact_mod_cast hB
  unfold resident
  constructor <;> linarith [h.1, h.2]

/-- Write one resident cell. The disk is untouched until a writeback. -/
def write (c : Cache B α) (p : ℤ) (a : α) : Cache B α :=
  { c with buffer := fun i => if c.origin + (i : ℤ) = p then a else c.buffer i }

@[simp] theorem resident_write (c : Cache B α) (p q : ℤ) (a : α) :
    resident (write c p a) q ↔ resident c q := Iff.rfl

theorem view_write (c : Cache B α) (p : ℤ) (a : α) (hp : resident c p) :
    view (write c p a) = Function.update (view c) p a := by
  funext q
  by_cases hq : resident c q
  · have hw : resident (write c p a) q := hq
    simp only [view, dif_pos hw, dif_pos hq]
    change (if c.origin + (slot c q hq : ℤ) = p then a else c.buffer (slot c q hq)) = _
    rw [slot_address]
    by_cases heq : q = p
    · subst q
      simp
    · simp [heq, Function.update_of_ne heq, view, hq]
  · have hq' : ¬ resident (write c p a) q := hq
    have hneq : q ≠ p := by intro h; subst q; exact hq hp
    rw [Function.update_of_ne hneq]
    simp only [view, dif_neg hq, dif_neg hq']
    rfl

/-- Write back the three buffer blocks. It changes only that window. -/
def flush (c : Cache B α) : Tape α := view c

/-- The ordinary disk primitive: read one aligned block. -/
def readBlock (disk : Tape α) (blockNumber : ℤ) (B : ℕ) : Fin B → α :=
  fun i => disk (blockNumber * (B : ℤ) + (i : ℤ))

/-- Each of the three portions of `load` is exactly one ordinary block read. -/
theorem load_block_contents (disk : Tape α) (p : ℤ) (j : Fin 3) (i : Fin B) :
    (load disk p B).buffer (finProdFinEquiv (j, i)) =
      readBlock disk (p / (B : ℤ) - 1 + (j : ℤ)) B i := by
  change disk ((p / (B : ℤ) - 1) * (B : ℤ) + ((i.val + B * j.val : ℕ) : ℤ)) = _
  simp only [readBlock, Nat.cast_add, Nat.cast_mul]
  congr 1
  ring

def inBlock (c : Cache B α) (j : Fin 3) (p : ℤ) : Prop :=
  c.origin + (j : ℤ) * (B : ℤ) ≤ p ∧
    p < c.origin + ((j : ℤ) + 1) * (B : ℤ)

instance (c : Cache B α) (j : Fin 3) (p : ℤ) : Decidable (inBlock c j p) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem block_in_window (c : Cache B α) (j : Fin 3) (p : ℤ)
    (h : inBlock c j p) : resident c p := by
  have hj0 : 0 ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j.val
  have hj3 : (j : ℤ) < 3 := by exact_mod_cast j.isLt
  have hb : 0 ≤ (B : ℤ) := by exact_mod_cast Nat.zero_le B
  unfold inBlock at h
  unfold resident
  constructor <;> nlinarith [mul_nonneg hj0 hb, mul_nonneg (show 0 ≤ 2 - (j : ℤ) by omega) hb]

/-- One block write from the cache. Only the selected contiguous `B` cells change. -/
def flushBlock (c : Cache B α) (j : Fin 3) (disk : Tape α) : Tape α := fun p =>
  if h : inBlock c j p then c.buffer (slot c p (block_in_window c j p h)) else disk p

def flushThree (c : Cache B α) : Tape α :=
  flushBlock c 2 (flushBlock c 1 (flushBlock c 0 c.disk))

/-- Thus `flush`, used by the executor, is exactly three actual block writes. -/
theorem flushThree_eq_flush (c : Cache B α) : flushThree c = flush c := by
  funext p
  by_cases hc : resident c p
  · have hp0 := hc.1
    have hp3 := hc.2
    have h0 : inBlock c 0 p ↔ c.origin ≤ p ∧ p < c.origin + (B : ℤ) := by
      simp [inBlock]
    have h1 : inBlock c 1 p ↔ c.origin + (B : ℤ) ≤ p ∧ p < c.origin + 2 * (B : ℤ) := by
      norm_num [inBlock]
    have h2 : inBlock c 2 p ↔ c.origin + 2 * (B : ℤ) ≤ p ∧ p < c.origin + 3 * (B : ℤ) := by
      norm_num [inBlock]
    by_cases hlast : c.origin + 2 * (B : ℤ) ≤ p
    · have hmem : inBlock c 2 p := h2.mpr ⟨hlast, hp3⟩
      simp only [flushThree, flushBlock, dif_pos hmem, flush, view, dif_pos hc]
    · have hn2 : ¬ inBlock c 2 p := by rw [h2]; omega
      by_cases hmid : c.origin + (B : ℤ) ≤ p
      · have hm : inBlock c 1 p := h1.mpr ⟨hmid, by omega⟩
        simp only [flushThree, flushBlock, dif_neg hn2, dif_pos hm, flush, view, dif_pos hc]
      · have hn1 : ¬ inBlock c 1 p := by rw [h1]; omega
        have hm : inBlock c 0 p := h0.mpr ⟨hp0, by omega⟩
        simp only [flushThree, flushBlock, dif_neg hn2, dif_neg hn1, dif_pos hm,
          flush, view, dif_pos hc]
  · have hn (j : Fin 3) : ¬ inBlock c j p := fun h => hc (block_in_window c j p h)
    simp only [flushThree, flushBlock, dif_neg (hn 2), dif_neg (hn 1), dif_neg (hn 0),
      flush, view, dif_neg hc]

theorem flush_outside (c : Cache B α) (p : ℤ) (h : ¬ resident c p) :
    flush c p = c.disk p := by simp [flush, view, h]

/-- Flush the old buffer and read three blocks around the new head. -/
def recenter (c : Cache B α) (p : ℤ) : Cache B α := load (flush c) p B

theorem view_recenter (c : Cache B α) (p : ℤ) :
    view (recenter c p) = view c := by exact view_load _ _ _

theorem recenter_resident (c : Cache B α) (p : ℤ) (hB : 0 < B) :
    resident (recenter c p) p := load_resident _ _ hB

/-- Left, stay, and right are the only tape head moves. -/
inductive Move where
  | left | stay | right
  deriving DecidableEq

def Move.delta : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

theorem move_bound (m : Move) : |m.delta| ≤ 1 := by cases m <;> norm_num [Move.delta]

/-- A local transition can depend on the symbol currently under the head. -/
abbrev Command (α : Type*) := α → α × Move

structure State (B : ℕ) (α : Type*) where
  cache : Cache B α
  head : ℤ
  /- The following fields count resource usage; they contain no data arrays. -/
  anchor : ℤ
  age : ℕ
  resets : ℕ

def initial (disk : Tape α) (p : ℤ) (B : ℕ) : State B α :=
  ⟨load disk p B, p, p, 0, 0⟩

def step (cmd : Command α) (s : State B α) : State B α :=
  let out := cmd (view s.cache s.head)
  let cache' := write s.cache s.head out.1
  let head' := s.head + out.2.delta
  if resident cache' head' then
    ⟨cache', head', s.anchor, s.age + 1, s.resets⟩
  else
    ⟨recenter cache' head', head', head', 0, s.resets + 1⟩

def logicalStep (cmd : Command α) (t : Tape α × ℤ) : Tape α × ℤ :=
  let out := cmd (t.1 t.2)
  (Function.update t.1 t.2 out.1, t.2 + out.2.delta)

def observable (s : State B α) : Tape α × ℤ := (view s.cache, s.head)

theorem step_correct (cmd : Command α) (s : State B α)
    (h : resident s.cache s.head) :
    observable (step cmd s) = logicalStep cmd (observable s) := by
  try dsimp only [step]
  split_ifs
  · simp only [observable, logicalStep, view_write _ _ _ h]
  · simp only [observable, logicalStep, view_recenter, view_write _ _ _ h]

theorem step_resident (cmd : Command α) (s : State B α) (hB : 0 < B) :
    resident (step cmd s).cache (step cmd s).head := by
  try dsimp only [step]
  split_ifs with h
  · exact h
  · exact recenter_resident _ _ hB

def run : List (Command α) → State B α → State B α
  | [], s => s
  | cmd :: rest, s => run rest (step cmd s)

def logicalRun : List (Command α) → Tape α × ℤ → Tape α × ℤ
  | [], s => s
  | cmd :: rest, s => logicalRun rest (logicalStep cmd s)

theorem run_correct (cmds : List (Command α)) (s : State B α)
    (hB : 0 < B) (h : resident s.cache s.head) :
    observable (run cmds s) = logicalRun cmds (observable s) := by
  induction cmds generalizing s with
  | nil => rfl
  | cons cmd rest ih =>
    simp only [run, logicalRun]
    rw [ih (step cmd s) (step_resident cmd s hB), step_correct cmd s h]

theorem initialized_run_correct (cmds : List (Command α)) (disk : Tape α)
    (p : ℤ) (hB : 0 < B) :
    observable (run cmds (initial disk p B)) = logicalRun cmds (disk, p) := by
  have h := run_correct cmds (initial disk p B) hB (load_resident disk p hB)
  simpa only [observable, initial, view_load] using h

theorem buffer_cells : Fintype.card (Fin (3 * B)) = 3 * B := Fintype.card_fin _

def Aligned (c : Cache B α) : Prop := ∃ k : ℤ, c.origin = k * (B : ℤ)

theorem load_aligned (disk : Tape α) (p : ℤ) (B : ℕ) : Aligned (load disk p B) :=
  ⟨p / (B : ℤ) - 1, rfl⟩

theorem step_aligned (cmd : Command α) (s : State B α) (h : Aligned s.cache) :
    Aligned (step cmd s).cache := by
  try dsimp only [step]
  split_ifs
  · exact h
  · exact load_aligned _ _ _

theorem run_aligned (cmds : List (Command α)) (s : State B α)
    (h : Aligned s.cache) : Aligned (run cmds s).cache := by
  induction cmds generalizing s with
  | nil => exact h
  | cons cmd rest ih => exact ih (step cmd s) (step_aligned cmd s h)

/-- `anchor` is the head position at the last reload; `age` counts steps since it. -/
structure Healthy (s : State B α) : Prop where
  present : resident s.cache s.head
  middle_lo : s.cache.origin + (B : ℤ) ≤ s.anchor
  middle_hi : s.anchor < s.cache.origin + 2 * (B : ℤ)
  distance : |s.head - s.anchor| ≤ (s.age : ℤ)

theorem initial_healthy (disk : Tape α) (p : ℤ) (hB : 0 < B) :
    Healthy (initial disk p B) := by
  have hm := load_middle disk p hB
  exact ⟨load_resident disk p hB, hm.1, hm.2, by simp [initial]⟩

theorem moved_distance (cmd : Command α) (s : State B α) (h : Healthy s) :
    |s.head + (cmd (view s.cache s.head)).2.delta - s.anchor| ≤
      (s.age : ℤ) + 1 := by
  calc
    _ ≤ |s.head - s.anchor| + |(cmd (view s.cache s.head)).2.delta| := by
      have ht := abs_add_le (s.head - s.anchor) ((cmd (view s.cache s.head)).2.delta)
      convert ht using 1; congr 1; ring
    _ ≤ (s.age : ℤ) + 1 := add_le_add h.distance (move_bound _)

theorem step_healthy (cmd : Command α) (s : State B α) (hB : 0 < B)
    (h : Healthy s) : Healthy (step cmd s) := by
  have hd := moved_distance cmd s h
  try dsimp only [step]
  split_ifs with hr
  · refine ⟨hr, h.middle_lo, h.middle_hi, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using hd
  · have hm := load_middle (flush (write s.cache s.head (cmd (view s.cache s.head)).1))
        (s.head + (cmd (view s.cache s.head)).2.delta) hB
    exact ⟨recenter_resident _ _ hB, hm.1, hm.2, by simp⟩

/-- The reset branch can only occur after at least a block's worth of steps. -/
theorem reset_requires_age (cmd : Command α) (s : State B α) (h : Healthy s)
    (hout : ¬ resident (write s.cache s.head (cmd (view s.cache s.head)).1)
      (s.head + (cmd (view s.cache s.head)).2.delta)) :
    B ≤ s.age + 1 := by
  let p := s.head + (cmd (view s.cache s.head)).2.delta
  have ho : p < s.cache.origin ∨ s.cache.origin + 3 * (B : ℤ) ≤ p := by
    rw [resident_write] at hout
    simpa only [resident, not_and_or, not_le, not_lt] using hout
  have hd : |p - s.anchor| ≤ (s.age : ℤ) + 1 := moved_distance cmd s h
  have hb : (B : ℤ) ≤ |p - s.anchor| := by
    rcases ho with hlo | hhi
    · have he := le_abs_self (s.anchor - p)
      rw [abs_sub_comm] at he
      linarith [h.middle_lo]
    · have he := le_abs_self (p - s.anchor)
      linarith [h.middle_hi]
  have : (B : ℤ) ≤ ((s.age + 1 : ℕ) : ℤ) := by push_cast; omega
  exact_mod_cast this

theorem step_work_bound (cmd : Command α) (s : State B α) (h : Healthy s)
    (elapsed : ℕ) (credit : s.resets * B + s.age ≤ elapsed) :
    (step cmd s).resets * B + (step cmd s).age ≤ elapsed + 1 := by
  try dsimp only [step]
  split_ifs with hr
  · try dsimp only
    omega
  · have hg := reset_requires_age cmd s h hr
    try dsimp only
    nlinarith

theorem run_work_bound (cmds : List (Command α)) (s : State B α)
    (hB : 0 < B) (h : Healthy s) (elapsed : ℕ)
    (credit : s.resets * B + s.age ≤ elapsed) :
    (run cmds s).resets * B + (run cmds s).age ≤ elapsed + cmds.length := by
  induction cmds generalizing s elapsed with
  | nil => simpa only [run, List.length_nil, Nat.add_zero] using credit
  | cons cmd rest ih =>
    have hn := ih (step cmd s) (step_healthy cmd s hB h) (elapsed + 1)
      (step_work_bound cmd s h elapsed credit)
    simpa only [run, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hn

theorem actual_reset_count_bound (cmds : List (Command α)) (disk : Tape α)
    (p : ℤ) (hB : 0 < B) :
    (run cmds (initial disk p B)).resets ≤ cmds.length / B := by
  have hc := run_work_bound cmds (initial disk p B) hB (initial_healthy disk p hB)
    0 (by simp [initial])
  apply (Nat.le_div_iff_mul_le hB).2
  omega

/-- A reset writes three old blocks and reads three new blocks. -/
def stepTransfers (cmd : Command α) (s : State B α) : ℕ :=
  if resident (write s.cache s.head (cmd (view s.cache s.head)).1)
      (s.head + (cmd (view s.cache s.head)).2.delta) then 0 else 6

def runTransfers : List (Command α) → State B α → ℕ
  | [], _ => 0
  | cmd :: rest, s => stepTransfers cmd s + runTransfers rest (step cmd s)

theorem step_transfers_exact (cmd : Command α) (s : State B α) :
    6 * s.resets + stepTransfers cmd s = 6 * (step cmd s).resets := by
  try dsimp only [step, stepTransfers]
  split_ifs
  · simp
  · simp; ring

theorem run_transfers_exact (cmds : List (Command α)) (s : State B α) :
    6 * s.resets + runTransfers cmds s = 6 * (run cmds s).resets := by
  induction cmds generalizing s with
  | nil => simp [run, runTransfers]
  | cons cmd rest ih =>
    simp only [runTransfers, run, ← Nat.add_assoc, step_transfers_exact]
    exact ih (step cmd s)

/-- Actual branch counts, including initial reads and final writeback.
No reset-gap or transfer-charge hypothesis occurs in this theorem. -/
theorem initialized_transfer_bound (cmds : List (Command α)) (disk : Tape α)
    (p : ℤ) (hB : 0 < B) :
    3 + runTransfers cmds (initial disk p B) + 3 ≤
      6 * (cmds.length / B + 1) := by
  have he := run_transfers_exact cmds (initial disk p B)
  have hb := actual_reset_count_bound cmds disk p hB
  simp only [initial, Nat.mul_zero, Nat.zero_add] at he
  simp only [initial] at hb ⊢
  omega

/- A controller makes the simulation input-adaptive. This general semantic
interface does not restrict its size. `TapeRuntime` provides finite-word
representations under explicit size bounds. The controller reads only the
current symbol; the reconstruction `view` is not supplied to it. -/
variable {Control : Type*}

abbrev Controller (Control α : Type*) := Control → α → Control × α × Move

def nextCommand (δ : Controller Control α) (q : Control) : Command α :=
  fun a => ((δ q a).2.1, (δ q a).2.2)

def controlledRun (δ : Controller Control α) : ℕ → Control → State B α →
    Control × State B α
  | 0, q, s => (q, s)
  | n + 1, q, s =>
    let q' := (δ q (view s.cache s.head)).1
    controlledRun δ n q' (step (nextCommand δ q) s)

def controlledLogicalRun (δ : Controller Control α) : ℕ → Control →
    Tape α × ℤ → Control × (Tape α × ℤ)
  | 0, q, t => (q, t)
  | n + 1, q, t =>
    let q' := (δ q (t.1 t.2)).1
    controlledLogicalRun δ n q' (logicalStep (nextCommand δ q) t)

theorem controlled_correct (δ : Controller Control α) (n : ℕ)
    (q : Control) (s : State B α) (hB : 0 < B) (hs : resident s.cache s.head) :
    let out := controlledRun δ n q s
    (out.1, observable out.2) = controlledLogicalRun δ n q (observable s) := by
  induction n generalizing q s with
  | zero => rfl
  | succ n ih =>
    simp only [controlledRun, controlledLogicalRun]
    have h := ih (δ q (view s.cache s.head)).1 (step (nextCommand δ q) s)
      (step_resident _ _ hB)
    rw [step_correct _ _ hs] at h
    exact h

theorem controlled_work_bound (δ : Controller Control α) (n : ℕ)
    (q : Control) (s : State B α) (hB : 0 < B) (hs : Healthy s)
    (elapsed : ℕ) (hc : s.resets * B + s.age ≤ elapsed) :
    (controlledRun δ n q s).2.resets * B + (controlledRun δ n q s).2.age ≤ elapsed + n := by
  induction n generalizing q s elapsed with
  | zero => simpa only [controlledRun, Nat.add_zero] using hc
  | succ n ih =>
    have h := ih (δ q (view s.cache s.head)).1 (step (nextCommand δ q) s)
      (step_healthy _ _ hB hs) (elapsed + 1) (step_work_bound _ _ hs elapsed hc)
    simpa only [controlledRun, Nat.add_assoc, Nat.add_comm 1] using h

def controlledTransfers (δ : Controller Control α) : ℕ → Control → State B α → ℕ
  | 0, _, _ => 0
  | n + 1, q, s =>
    stepTransfers (nextCommand δ q) s +
      controlledTransfers δ n (δ q (view s.cache s.head)).1 (step (nextCommand δ q) s)

theorem controlled_transfers_exact (δ : Controller Control α) (n : ℕ)
    (q : Control) (s : State B α) :
    6 * s.resets + controlledTransfers δ n q s = 6 * (controlledRun δ n q s).2.resets := by
  induction n generalizing q s with
  | zero => simp [controlledTransfers, controlledRun]
  | succ n ih =>
    simp only [controlledTransfers, controlledRun, ← Nat.add_assoc, step_transfers_exact]
    exact ih _ _

theorem initialized_controller_transfer_bound (δ : Controller Control α) (n : ℕ)
    (q : Control) (disk : Tape α) (p : ℤ) (hB : 0 < B) :
    3 + controlledTransfers δ n q (initial disk p B) + 3 ≤ 6 * (n / B + 1) := by
  have hw := controlled_work_bound δ n q (initial disk p B) hB
    (initial_healthy disk p hB) 0 (by simp [initial])
  have he := controlled_transfers_exact δ n q (initial disk p B)
  have hr : (controlledRun δ n q (initial disk p B)).2.resets ≤ n / B := by
    apply (Nat.le_div_iff_mul_le hB).2
    omega
  simp only [initial, Nat.mul_zero, Nat.zero_add] at he
  simp only [initial] at hr ⊢
  omega

end CSL.TapeMachine


