-- Prove2me | Definitions.Def_CSL_Shared_Programs_Normalization
-- name    : CSL_Shared_Programs_Normalization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:09:44.329015+00:00
-- url     : https://prove2.me/theorems/de6ebb1e-70b3-46a6-8626-926a59477506
-- title:
--   Coded sorting library: Shared / Programs / Normalization
-- statement:
--   Module `CodedSorting.Shared.Programs.Normalization` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Explicit block-size simulation for Appendix A
--
--   A logical block is represented by the blockPrefix of its own physical block.
--   The simulator has the SAME finite work memory plus ONE physical block buffer.
--   This file defines read, write, and local-computation transitions, and proves
--   simulation for arbitrary memory-dependent command policies and finite runs.
--   The I/O cost is computed from the actual transition constructors, not supplied
--   as a hypothesis. Compact-layout conversion and logarithmic parameter transfer
--   are not proved by this module.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.Normalization

import Definitions.Def_CSL_Compat
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Explicit block-size simulation for Appendix A

A logical block is represented by the blockPrefix of its own physical block.
The simulator has the SAME finite work memory plus ONE physical block buffer.
This file defines read, write, and local-computation transitions, and proves
simulation for arbitrary memory-dependent command policies and finite runs.
The I/O cost is computed from the actual transition constructors, not supplied
as a hypothesis. Compact-layout conversion and logarithmic parameter transfer
are not proved by this module.
-/

namespace CSL.Normalization

abbrev Words (n : ℕ) (Word : Type*) := Fin n → Word
abbrev Disk (blocks size : ℕ) (Word : Type*) := Fin blocks → Words size Word

variable {Word : Type*} {L b B D : ℕ}

/-- A contiguous RAM window fitting inside the fixed L-word work memory. -/
structure Window (L b : ℕ) where
  base : ℕ
  fits : base + b ≤ L

/-- Copy a block into the designated existing RAM window. -/
def load (ram : Words L Word) (w : Window L b) (block : Words b Word) :
    Words L Word := fun j =>
  if h : w.base ≤ j.val ∧ j.val < w.base + b then
    block ⟨j.val - w.base, by omega⟩
  else ram j

/-- Read the designated RAM window without allocating another RAM array. -/
def slice (ram : Words L Word) (w : Window L b) : Words b Word := fun j =>
  ram ⟨w.base + j.val, by have := w.fits; have := j.isLt; omega⟩

/-- Valid logical data is the blockPrefix of its own physical block. -/
def blockPrefix (h : b ≤ B) (block : Words B Word) : Words b Word :=
  fun j => block (Fin.castLE h j)

/-- Fill one physical transfer buffer; the unused suffix is irrelevant. -/
def pack (padding : Word) (block : Words b Word) : Words B Word := fun j =>
  if h : j.val < b then block ⟨j.val, h⟩ else padding

@[simp] theorem prefix_pack (h : b ≤ B) (padding : Word) (block : Words b Word) :
    blockPrefix h (pack padding block) = block := by
  funext j
  simp [blockPrefix, pack, j.isLt]

structure LogicalState (L b D : ℕ) (Word : Type*) where
  ram : Words L Word
  disk : Disk D b Word

structure PhysicalState (L B D : ℕ) (Word : Type*) where
  ram : Words L Word
  buffer : Words B Word
  disk : Disk D B Word

/-- An ordinary I/O machine instruction. The local operation changes only the
existing L-word RAM. Disk accesses cannot occur inside that constructor. -/
inductive Command (L b D : ℕ) (Word : Type*)
  | localOp (f : Words L Word → Words L Word)
  | read (address : Fin D) (window : Window L b)
  | write (address : Fin D) (window : Window L b)

def transferCost : Command L b D Word → ℕ
  | .localOp _ => 0
  | .read _ _ => 1
  | .write _ _ => 1

def logicalStep (cmd : Command L b D Word) (s : LogicalState L b D Word) :
    LogicalState L b D Word :=
  match cmd with
  | .localOp f => {s with ram := f s.ram}
  | .read i w => {s with ram := load s.ram w (s.disk i)}
  | .write i w => {s with disk := Function.update s.disk i (slice s.ram w)}

/-- A read loads exactly one physical block, then copies its blockPrefix into RAM.
A write fills the existing physical buffer and writes exactly one block.
Every logical block has a distinct dedicated physical block, so writes do
not require a read-modify-write of somebody else's logical data. -/
def physicalStep (h : b ≤ B) (padding : Word)
    (cmd : Command L b D Word) (s : PhysicalState L B D Word) :
    PhysicalState L B D Word :=
  match cmd with
  | .localOp f => {s with ram := f s.ram}
  | .read i w =>
      {s with ram := load s.ram w (blockPrefix h (s.disk i)), buffer := s.disk i}
  | .write i w =>
      let block : Words B Word := pack padding (slice s.ram w)
      {s with buffer := block, disk := Function.update s.disk i block}

/-- Physical primitives separate actual disk transfers from RAM-only copies. -/
inductive PhysicalCommand (L b D : ℕ) (Word : Type*)
  | localOp (f : Words L Word → Words L Word)
  | fetch (address : Fin D)
  | copyPrefix (window : Window L b)
  | stageWrite (window : Window L b)
  | flush (address : Fin D)

def primitiveCost : PhysicalCommand L b D Word → ℕ
  | .fetch _ => 1
  | .flush _ => 1
  | .localOp _ => 0
  | .copyPrefix _ => 0
  | .stageWrite _ => 0

def primitiveStep (h : b ≤ B) (padding : Word)
    (cmd : PhysicalCommand L b D Word) (s : PhysicalState L B D Word) :
    PhysicalState L B D Word :=
  match cmd with
  | .localOp f => {s with ram := f s.ram}
  | .fetch i => {s with buffer := s.disk i}
  | .copyPrefix w => {s with ram := load s.ram w (blockPrefix h s.buffer)}
  | .stageWrite w => {s with buffer := pack padding (slice s.ram w)}
  | .flush i => {s with disk := Function.update s.disk i s.buffer}

/-- The compiler makes every physical transfer explicit. -/
def compileCommand : Command L b D Word → List (PhysicalCommand L b D Word)
  | .localOp f => [.localOp f]
  | .read i w => [.fetch i, .copyPrefix w]
  | .write i w => [.stageWrite w, .flush i]

def executePrimitives (h : b ≤ B) (padding : Word) :
    List (PhysicalCommand L b D Word) → PhysicalState L B D Word →
      PhysicalState L B D Word
  | [], s => s
  | cmd :: rest, s => executePrimitives h padding rest (primitiveStep h padding cmd s)

def primitiveListCost : List (PhysicalCommand L b D Word) → ℕ
  | [] => 0
  | cmd :: rest => primitiveCost cmd + primitiveListCost rest

theorem compiled_step_eq (h : b ≤ B) (padding : Word)
    (cmd : Command L b D Word) (s : PhysicalState L B D Word) :
    executePrimitives h padding (compileCommand cmd) s = physicalStep h padding cmd s := by
  cases cmd <;> rfl

/-- Actual fetch/flush counting, not a postulated physical cost. -/
theorem compiled_cost_eq (cmd : Command L b D Word) :
    primitiveListCost (compileCommand cmd) = transferCost cmd := by
  cases cmd <;> rfl

/-- RAM agrees word for word; every disk block agrees on its valid blockPrefix.
There is deliberately no condition on the physical buffer or padding. -/
def Represents (h : b ≤ B) (s : LogicalState L b D Word)
    (t : PhysicalState L B D Word) : Prop :=
  s.ram = t.ram ∧ ∀ i, s.disk i = blockPrefix h (t.disk i)

/-- Actual transition refinement for all three instruction kinds. -/
theorem step_represents (h : b ≤ B) (padding : Word)
    (cmd : Command L b D Word)
    (s : LogicalState L b D Word) (t : PhysicalState L B D Word)
    (hst : Represents h s t) :
    Represents h (logicalStep cmd s) (physicalStep h padding cmd t) := by
  rcases hst with ⟨hram, hdisk⟩
  cases cmd with
  | localOp f =>
    constructor
    · simp [logicalStep, physicalStep, hram]
    · exact hdisk
  | read i w =>
    constructor
    · change load s.ram w (s.disk i) = load t.ram w (blockPrefix h (t.disk i))
      rw [hram, hdisk i]
    · exact hdisk
  | write i w =>
    constructor
    · exact hram
    · intro j
      by_cases hj : j = i
      · subst j
        simp [logicalStep, physicalStep, prefix_pack, hram]
      · simp [logicalStep, physicalStep, hj, hdisk j]

/-- The policy may inspect all current work memory, so the instruction
sequence need not be oblivious. Program counters can be stored in that RAM.
`none` is termination. A finite fuel is only an observation horizon. -/
abbrev Policy (L b D : ℕ) (Word : Type*) :=
  Words L Word → Option (Command L b D Word)

def runLogical (policy : Policy L b D Word) :
    ℕ → LogicalState L b D Word → LogicalState L b D Word × ℕ
  | 0, s => (s, 0)
  | fuel + 1, s =>
    match policy s.ram with
    | none => (s, 0)
    | some cmd =>
      let result := runLogical policy fuel (logicalStep cmd s)
      (result.1, transferCost cmd + result.2)

def runPhysical (h : b ≤ B) (padding : Word) (policy : Policy L b D Word) :
    ℕ → PhysicalState L B D Word → PhysicalState L B D Word × ℕ
  | 0, s => (s, 0)
  | fuel + 1, s =>
    match policy s.ram with
    | none => (s, 0)
    | some cmd =>
      let result := runPhysical h padding policy fuel
        (executePrimitives h padding (compileCommand cmd) s)
      (result.1, primitiveListCost (compileCommand cmd) + result.2)

/-- Every finite, possibly data-dependent execution is simulated with the
EXACT SAME number of block transfers. No I/O bound is assumed here. -/
theorem run_represents_and_cost (h : b ≤ B) (padding : Word)
    (policy : Policy L b D Word) (fuel : ℕ)
    (s : LogicalState L b D Word) (t : PhysicalState L B D Word)
    (hst : Represents h s t) :
    Represents h (runLogical policy fuel s).1
      (runPhysical h padding policy fuel t).1 ∧
    (runLogical policy fuel s).2 = (runPhysical h padding policy fuel t).2 := by
  induction fuel generalizing s t with
  | zero => exact ⟨hst, rfl⟩
  | succ fuel ih =>
    have hram := hst.1
    cases hc : policy s.ram with
    | none =>
      have hc' : policy t.ram = none := by rw [← hram]; exact hc
      simpa only [runLogical, runPhysical, hc, hc'] using And.intro hst (show (0 : ℕ) = 0 from rfl)
    | some cmd =>
      have hc' : policy t.ram = some cmd := by rw [← hram]; exact hc
      have hr := ih (logicalStep cmd s) (physicalStep h padding cmd t)
        (step_represents h padding cmd s t hst)
      simp only [runLogical, runPhysical, hc, hc', compiled_step_eq, compiled_cost_eq]
      exact ⟨hr.1, congrArg (fun cost => transferCost cmd + cost) hr.2⟩

/-- The same policy halts in both represented states. -/
theorem termination_agrees (h : b ≤ B) (policy : Policy L b D Word)
    (s : LogicalState L b D Word) (t : PhysicalState L B D Word)
    (hst : Represents h s t) : (policy s.ram = none) ↔ (policy t.ram = none) := by
  rw [hst.1]

/-- Initial encoded disk for an arbitrary logical disk and arbitrary RAM. -/
def encodeState (padding : Word) (s : LogicalState L b D Word) :
    PhysicalState L B D Word :=
  ⟨s.ram, fun _ => padding, fun i => pack padding (s.disk i)⟩

theorem initial_encoding_represents (h : b ≤ B) (padding : Word)
    (s : LogicalState L b D Word) : Represents h s (encodeState padding s) := by
  constructor
  · rfl
  · intro i
    simp [encodeState]

/-- Resident storage consists of the logical RAM and one transfer buffer.
This counts physical words, not logical blocks. -/
theorem resident_word_count :
    Fintype.card (Sum (Fin L) (Fin B)) = L + B := by simp

/-- Extra fixed control words fit in the remaining quarter of physical RAM. -/
theorem physical_memory_budget (M B control : ℕ)
    (hblocks : 2 * B ≤ M) (hcontrol : 4 * control ≤ M) :
    M / 4 + B + control ≤ M := by omega

def logicalBlockSize (B K : ℕ) : ℕ := max 1 (B / K)

theorem logical_block_positive (B K : ℕ) : 0 < logicalBlockSize B K := by
  have h : 1 ≤ logicalBlockSize B K := le_max_left _ _
  omega

theorem logical_block_le_physical (B K : ℕ) (hB : 0 < B) :
    logicalBlockSize B K ≤ B := by
  exact max_le (by omega) (Nat.div_le_self B K)

/-- Concrete normalization ratio with integer floors. -/
theorem normalized_ratio (M B R K : ℕ)
    (hK : 4 * R ≤ K) (hM : 4 * R ≤ M) (hB : B ≤ M) :
    R * logicalBlockSize B K ≤ M / 4 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).2
  by_cases hq : 1 ≤ B / K
  · rw [logicalBlockSize, max_eq_right hq]
    calc
      R * (B / K) * 4 = (4 * R) * (B / K) := by ring
      _ ≤ K * (B / K) := Nat.mul_le_mul_right _ hK
      _ ≤ B := by simpa [Nat.mul_comm] using Nat.div_mul_le_self B K
      _ ≤ M := hB
  · have hq' : B / K ≤ 1 := by omega
    rw [logicalBlockSize, max_eq_left hq']
    simpa [Nat.mul_comm] using hM

/-- Dedicated physical blocks expand space by at most a fixed factor 2K. -/
theorem block_expansion_bound (B K : ℕ) (hK : 0 < K) :
    B ≤ 2 * K * logicalBlockSize B K := by
  have hq : B / K ≤ logicalBlockSize B K := le_max_right _ _
  have h1 : 1 ≤ logicalBlockSize B K := le_max_left _ _
  calc
    B ≤ K * (B / K + 1) := Nat.le_of_lt (Nat.lt_mul_div_succ B hK)
    _ ≤ K * (2 * logicalBlockSize B K) := Nat.mul_le_mul_left K (by omega)
    _ = 2 * K * logicalBlockSize B K := by ring

theorem disk_space_expansion (blocks B K : ℕ) (hK : 0 < K) :
    blocks * B ≤ (2 * K) * (blocks * logicalBlockSize B K) := by
  calc
    blocks * B ≤ blocks * (2 * K * logicalBlockSize B K) :=
      Nat.mul_le_mul_left blocks (block_expansion_bound B K hK)
    _ = (2 * K) * (blocks * logicalBlockSize B K) := by ring

end CSL.Normalization


