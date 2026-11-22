-- Prove2me | Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part04
-- name    : VehicleRoutingSurvey_RuralPostman1979_Part04
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T13:59:47.799014+00:00
-- url     : https://prove2.me/theorems/ba13d423-8323-4e74-aff2-8b5f7785dc5f
-- title:
--   Rural postman algorithm — Required-component traversal and minimum connector-tree updates
-- statement:
--   This module supplies the Lean definitions and checked auxiliary results for required-component traversal and minimum connector-tree updates in the Table 3 proof. It uses the mission’s rural-run and arithmetic-RAM model.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Mathlib.Tactic.Ring
import Mathlib.Data.List.Perm.Subperm
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part01
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part02
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part03

/-! runtime/RequiredLabelCell.lean -/
section RppSource_RequiredLabelCell
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Relabel the indexed vertex when the current pair is present and the
vertex is in the class being merged. Each branch executes nine instructions. -/
def labelMergeCell : List ArithmeticInstruction :=
  [.natAdd 28 24 7, .natLoad 29 28, .natSub 30 29 26, .natSub 31 26 29,
    .natAdd 30 30 31, .natSub 31 6 27, .natAdd 32 30 31,
    .natBranch 32 33 9 8, .jump 10, .natStore 28 25]

def relabelValue (enabled : Bool) (replacement retired old : ℕ) : ℕ :=
  if enabled = true ∧ old = retired then replacement else old

/-- Registers 24–27 hold the label table base, replacement and retired
labels, and the required-pair bit. Register 33 holds zero. -/
structure LabelMergeFrame (n base replacement retired : ℕ) (enabled : Bool)
    (s : ArithmeticState) : Prop where
  dimension : s.nr 5 = n
  one : s.nr 6 = 1
  tableBase : s.nr 24 = base
  newLabel : s.nr 25 = replacement
  oldLabel : s.nr 26 = retired
  bit : s.nr 27 = if enabled then 1 else 0
  zero : s.nr 33 = 0

def FixedLabelMergeRegisters (s t : ArithmeticState) : Prop :=
  ∀ r, r < 28 ∨ 32 < r → t.nr r = s.nr r

theorem labelMergeCell_correct {n base replacement retired : ℕ} {enabled : Bool}
    {s : ArithmeticState} (frame : LabelMergeFrame n base replacement retired enabled s)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns labelMergeCell 9 s t ∧ t.halted = false ∧
      FixedLabelMergeRegisters s t ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      t.nm = Function.update s.nm (base + s.nr 7)
        (relabelValue enabled replacement retired (s.nm (base + s.nr 7))) := by
  let address := s.nr 24 + s.nr 7
  let old := s.nm address
  let difference := (old - s.nr 26) + (s.nr 26 - old)
  let inactive := s.nr 6 - s.nr 27
  let verdict := difference + inactive
  let readRegisters := Function.update (Function.update (Function.update (Function.update
    (Function.update s.nr 28 address) 29 old) 30 (old - s.nr 26))
    31 (s.nr 26 - old)) 30 difference
  let registers := Function.update (Function.update readRegisters 31 inactive) 32 verdict
  let t := {s with
    pc := 10
    nr := registers
    nm := Function.update s.nm address (relabelValue enabled replacement retired old)}
  have condition : verdict ≤ s.nr 33 ↔ enabled = true ∧ old = retired := by
    cases enabled <;>
      simp [verdict, inactive, difference, frame.one, frame.bit, frame.zero, frame.oldLabel] <;> omega
  let middle := {s with pc := 7, nr := registers}
  have prepared : (arithmeticStep labelMergeCell)^[7] s = middle := by
    simp [middle, registers, readRegisters, labelMergeCell, arithmeticStep, entry, running,
      Function.iterate_succ_apply', address, old, difference, inactive, verdict]
  have test : middle.nr 32 ≤ middle.nr 33 ↔ enabled = true ∧ old = retired := by
    simpa [middle, registers, readRegisters] using condition
  have atBranch : arithmeticStep labelMergeCell middle =
      {middle with pc := if enabled = true ∧ old = retired then 9 else 8} := by
    have ready : middle.halted = false := running
    have here : middle.pc = 7 := rfl
    simp [arithmeticStep, labelMergeCell, ready, here, test]
  have executes : BlockRuns labelMergeCell 9 s t := by
    refine ⟨?_, ?_, rfl⟩
    · intro i hi
      by_cases before : i < 8
      · interval_cases i <;> simp [labelMergeCell, arithmeticStep, entry, running,
          Function.iterate_succ_apply']
      · have atEight : i = 8 := by omega
        subst i
        rw [show (8 : ℕ) = 7 + 1 by decide, Function.iterate_succ_apply', prepared, atBranch]
        by_cases update : enabled = true ∧ old = retired <;> simp [update, labelMergeCell]
    · rw [show (9 : ℕ) = 2 + 7 by decide, Function.iterate_add_apply, prepared]
      rw [show (arithmeticStep labelMergeCell)^[2] middle =
        arithmeticStep labelMergeCell (arithmeticStep labelMergeCell middle) by rfl, atBranch]
      by_cases update : enabled = true ∧ old = retired
      · rw [if_pos update]
        simp [t, middle, registers, readRegisters, labelMergeCell, arithmeticStep, running,
          relabelValue, if_pos update, frame.newLabel]
      · rw [if_neg update]
        simp [t, middle, labelMergeCell, arithmeticStep, running, relabelValue, if_neg update,
          Function.update_eq_self] <;> rfl
  refine ⟨t, executes, running, ?_, rfl, rfl, ?_⟩
  · intro r fixed
    simp [t, registers, readRegisters, Function.update_of_ne (show r ≠ 28 by omega),
      Function.update_of_ne (show r ≠ 29 by omega), Function.update_of_ne (show r ≠ 30 by omega),
      Function.update_of_ne (show r ≠ 31 by omega), Function.update_of_ne (show r ≠ 32 by omega)]
  · simp [t, address, old, frame.tableBase]

end VehicleRoutingSurvey.Routing
end RppSource_RequiredLabelCell

/-! runtime/RequiredLabelPass.lean -/
section RppSource_RequiredLabelPass
namespace VehicleRoutingSurvey.Routing

def labelMergePass : List ArithmeticInstruction :=
  countedLoopFromZero 6 7 5 labelMergeCell

def FixedLabelPassRegisters (s t : ArithmeticState) : Prop :=
  ∀ r, r ≠ 7 → (r < 28 ∨ 32 < r) → t.nr r = s.nr r

private structure LabelPassState (initial : ArithmeticState) (base replacement retired : ℕ)
    (enabled : Bool) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 7 = i
  fixed : FixedLabelPassRegisters initial s
  realMemory : s.rm = initial.rm
  realRegisters : s.rr = initial.rr
  naturalMemory : ∀ k, s.nm k = if base ≤ k ∧ k < base + i then
    relabelValue enabled replacement retired (initial.nm k) else initial.nm k

/-- An enabled pass updates exactly the retired class. A disabled pass
leaves the label table unchanged. Both take twelve instructions per vertex
and two fixed instructions. -/
theorem labelMergePass_correct {n base replacement retired : ℕ} {enabled : Bool}
    {s : ArithmeticState} (frame : LabelMergeFrame n base replacement retired enabled s)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns labelMergePass (12 * n + 2) s t ∧ t.halted = false ∧
      FixedLabelPassRegisters s t ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ k, t.nm k = if base ≤ k ∧ k < base + n then
        relabelValue enabled replacement retired (s.nm k) else s.nm k := by
  let inv := LabelPassState s base replacement retired enabled
  let first := {s with pc := 0, nr := Function.update s.nr 7 0}
  have initial : inv 0 first := by
    refine ⟨rfl, running, by simp [first], ?_, rfl, rfl, fun k => by simp [first]⟩
    intro r different _
    simp [first, Function.update_of_ne different]
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 5 = n :=
    ⟨hm.entry, hm.running, hm.index, (hm.fixed 5 (by decide) (by decide)).trans frame.dimension⟩
  have iterate (i : ℕ) (_ : i < n) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns labelMergeCell 9 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)} := by
    have atFrame : LabelMergeFrame n base replacement retired enabled m :=
      ⟨(hm.fixed 5 (by decide) (by decide)).trans frame.dimension,
        (hm.fixed 6 (by decide) (by decide)).trans frame.one,
        (hm.fixed 24 (by decide) (by decide)).trans frame.tableBase,
        (hm.fixed 25 (by decide) (by decide)).trans frame.newLabel,
        (hm.fixed 26 (by decide) (by decide)).trans frame.oldLabel,
        (hm.fixed 27 (by decide) (by decide)).trans frame.bit,
        (hm.fixed 33 (by decide) (by decide)).trans frame.zero⟩
    obtain ⟨t, run, ready, fixed, realMemory, realRegisters, naturalMemory⟩ :=
      labelMergeCell_correct atFrame hm.entry hm.running
    have before : m.nm (base + i) = s.nm (base + i) := by
      rw [hm.naturalMemory, if_neg (by omega)]
    refine ⟨t, run, ready, rfl, ready, ?_, ?_, realMemory.trans hm.realMemory,
      realRegisters.trans hm.realRegisters, ?_⟩
    · change Function.update t.nr 7 (t.nr 7 + t.nr 6) 7 = i + 1
      rw [Function.update_self, fixed 7 (by decide), fixed 6 (by decide), hm.index, atFrame.one]
    · intro r different preserved
      change Function.update t.nr 7 (t.nr 7 + t.nr 6) r = s.nr r
      rw [Function.update_of_ne different, fixed r preserved, hm.fixed r different preserved]
    · intro k
      change t.nm k = _
      rw [naturalMemory, hm.index, before]
      by_cases latest : k = base + i
      · subst k
        rw [Function.update_self, if_pos (by omega)]
      · rw [Function.update_of_ne latest, hm.naturalMemory]
        have same : (base ≤ k ∧ k < base + (i + 1)) ↔ (base ≤ k ∧ k < base + i) := by omega
        simp only [same]
  obtain ⟨last, complete, run⟩ :=
    countedLoopFromZero_correct 6 7 5 n 9 labelMergeCell inv entry running initial control iterate
  let finish := relocateState 1 {last with pc := (countedLoop 6 7 5 labelMergeCell).length}
  have ticks : 1 + (n * (9 + 3) + 1) = 12 * n + 2 := by omega
  refine ⟨finish, by simpa only [labelMergePass, ticks] using run, complete.running, complete.fixed,
    complete.realMemory, complete.realRegisters, complete.naturalMemory⟩

end VehicleRoutingSurvey.Routing
end RppSource_RequiredLabelPass

/-! runtime/RequiredLabelPair.lean -/
section RppSource_RequiredLabelPair
namespace VehicleRoutingSurvey.Routing

/-- Read the required-pair bit and the two current endpoint labels. The
pair's row and column indices are in registers 34 and 35. -/
private def readLabelPair : List ArithmeticInstruction :=
  [.natAdd 36 3 34, .natLoad 36 36, .natAdd 36 36 35, .natAdd 36 37 36, .natLoad 27 36,
    .natAdd 36 24 34, .natLoad 25 36, .natAdd 36 24 35, .natLoad 26 36]

private def readLabelPairState (s : ArithmeticState) : ArithmeticState :=
  let bit := s.nr 37 + (s.nm (s.nr 3 + s.nr 34) + s.nr 35)
  let left := s.nr 24 + s.nr 34
  let right := s.nr 24 + s.nr 35
  let afterBit := Function.update (Function.update s.nr 36 bit) 27 (s.nm bit)
  let afterLeft := Function.update (Function.update afterBit 36 left) 25 (s.nm left)
  let afterRight := Function.update (Function.update afterLeft 36 right) 26 (s.nm right)
  {s with pc := 9, nr := afterRight}

private theorem readLabelPair_runs {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) : BlockRuns readLabelPair 9 s (readLabelPairState s) := by
  refine ⟨?_, ?_, rfl⟩
  · intro i hi
    interval_cases i <;> simp [readLabelPair, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [readLabelPairState, readLabelPair, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Function.update_idem]

structure LabelPairFrame (n rows matrix labels bits : ℕ)
    (required : Fin n → Fin n → Bool) (s : ArithmeticState) : Prop where
  floyd : FloydFrame n rows matrix s
  labelBase : s.nr 24 = labels
  bitBase : s.nr 37 = bits
  zero : s.nr 33 = 0
  pairBits : ∀ u v : Fin n, s.nm (bits + n * u.val + v.val) = if required u v then 1 else 0
  rowsBeforeLabels : rows + n ≤ labels
  bitsBeforeLabels : ∀ u v : Fin n, bits + n * u.val + v.val < labels

def mergeLabelPairBlock : List ArithmeticInstruction :=
  appendBlock readLabelPair labelMergePass

def mergeLabelPairMemory {n : ℕ} (labels : ℕ) (enabled : Bool) (u v : Fin n)
    (memory : ℕ → ℕ) : ℕ → ℕ :=
  fun k => if labels ≤ k ∧ k < labels + n then
    relabelValue enabled (memory (labels + u.val)) (memory (labels + v.val)) (memory k)
  else memory k

theorem mergeLabelPairMemory_labelView {n : ℕ} (labels : ℕ) (enabled : Bool) (u v : Fin n)
    (memory : ℕ → ℕ) :
    (fun w : Fin n => mergeLabelPairMemory labels enabled u v memory (labels + w.val)) =
      if enabled then mergeComponentLabels (fun w => memory (labels + w.val)) u v
      else fun w => memory (labels + w.val) := by
  funext w
  have within : labels ≤ labels + w.val ∧ labels + w.val < labels + n :=
    ⟨Nat.le_add_right _ _, Nat.add_lt_add_left w.isLt _⟩
  cases enabled <;> simp [mergeLabelPairMemory, relabelValue, mergeComponentLabels, within]

/-- Read one pair and apply precisely its optional label merge. Entries
outside the label array, including the row offsets and pair bits used in
later iterations, remain intact. -/
theorem mergeLabelPairBlock_correct {n rows matrix labels bits : ℕ}
    {required : Fin n → Fin n → Bool} {s : ArithmeticState}
    (frame : LabelPairFrame n rows matrix labels bits required s)
    (entry : s.pc = 0) (running : s.halted = false)
    (u v : Fin n) (row : s.nr 34 = u.val) (column : s.nr 35 = v.val) :
    ∃ t, BlockRuns mergeLabelPairBlock (12 * n + 11) s t ∧ t.halted = false ∧
      LabelPairFrame n rows matrix labels bits required t ∧
      t.nr 34 = u.val ∧ t.nr 35 = v.val ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      t.nm = mergeLabelPairMemory labels (required u v) u v s.nm := by
  let read := readLabelPairState s
  let ready := {read with pc := 0}
  have nextReg (r : ℕ) (different : r ≠ 25 ∧ r ≠ 26 ∧ r ≠ 27 ∧ r ≠ 36) : ready.nr r = s.nr r := by
    simp [ready, read, readLabelPairState, Function.update_of_ne different.1,
      Function.update_of_ne different.2.1, Function.update_of_ne different.2.2.1,
      Function.update_of_ne different.2.2.2]
  have mergeFrame : LabelMergeFrame n labels (s.nm (labels + u.val)) (s.nm (labels + v.val))
      (required u v) ready := by
    refine ⟨(nextReg 5 (by decide)).trans frame.floyd.dimension,
      (nextReg 6 (by decide)).trans frame.floyd.one,
      (nextReg 24 (by decide)).trans frame.labelBase, ?_, ?_, ?_,
      (nextReg 33 (by decide)).trans frame.zero⟩
    · simp [ready, read, readLabelPairState, frame.labelBase, row]
    · simp [ready, read, readLabelPairState, frame.labelBase, column]
    · simp [ready, read, readLabelPairState, frame.bitBase, frame.floyd.tableBase,
        frame.floyd.rows _ u.isLt, row, column, ← Nat.add_assoc, frame.pairBits]
  obtain ⟨merged, pass, stillRunning, fixed, realMemory, realRegisters, naturalMemory⟩ :=
    labelMergePass_correct mergeFrame rfl running
  let finish := relocateState readLabelPair.length merged
  have executes := (readLabelPair_runs entry running).append pass
  have memory : finish.nm = mergeLabelPairMemory labels (required u v) u v s.nm :=
    funext naturalMemory
  have keeps (r : ℕ) (index : r ≠ 7) (passStable : r < 28 ∨ 32 < r)
      (readStable : r ≠ 25 ∧ r ≠ 26 ∧ r ≠ 27 ∧ r ≠ 36) : finish.nr r = s.nr r :=
    (fixed r index passStable).trans (nextReg r readStable)
  have same (k : ℕ) (before : k < labels) : finish.nm k = s.nm k := by
    rw [memory, mergeLabelPairMemory, if_neg (fun range => (not_le.mpr before) range.1)]
  have finalFrame : LabelPairFrame n rows matrix labels bits required finish :=
    ⟨⟨(keeps 3 (by decide) (by decide) (by decide)).trans frame.floyd.tableBase,
      (keeps 4 (by decide) (by decide) (by decide)).trans frame.floyd.matrixBase,
      (keeps 5 (by decide) (by decide) (by decide)).trans frame.floyd.dimension,
      (keeps 6 (by decide) (by decide) (by decide)).trans frame.floyd.one,
      fun i hi => (same _ ((Nat.add_lt_add_left hi _).trans_le frame.rowsBeforeLabels)).trans
        (frame.floyd.rows i hi)⟩,
      (keeps 24 (by decide) (by decide) (by decide)).trans frame.labelBase,
      (keeps 37 (by decide) (by decide) (by decide)).trans frame.bitBase,
      (keeps 33 (by decide) (by decide) (by decide)).trans frame.zero,
      fun i j => (same _ (frame.bitsBeforeLabels i j)).trans (frame.pairBits i j),
      frame.rowsBeforeLabels, frame.bitsBeforeLabels⟩
  have ticks : 9 + (12 * n + 2) = 12 * n + 11 := by omega
  exact ⟨finish, by simpa only [mergeLabelPairBlock, ticks] using executes, stillRunning, finalFrame,
    (keeps 34 (by decide) (by decide) (by decide)).trans row,
    (keeps 35 (by decide) (by decide) (by decide)).trans column, realMemory, realRegisters, memory⟩

end VehicleRoutingSurvey.Routing
end RppSource_RequiredLabelPair

/-! runtime/RequiredLabelSweep.lean -/
section RppSource_RequiredLabelSweep
namespace VehicleRoutingSurvey.Routing

private theorem LabelPairFrame.copyControl {n rows matrix labels bits : ℕ}
    {required : Fin n → Fin n → Bool} {s t : ArithmeticState}
    (frame : LabelPairFrame n rows matrix labels bits required s)
    (fixed : ∀ r, r ≠ 34 → r ≠ 35 → t.nr r = s.nr r) (natural : t.nm = s.nm) :
    LabelPairFrame n rows matrix labels bits required t :=
  ⟨⟨(fixed 3 (by decide) (by decide)).trans frame.floyd.tableBase,
    (fixed 4 (by decide) (by decide)).trans frame.floyd.matrixBase,
    (fixed 5 (by decide) (by decide)).trans frame.floyd.dimension,
    (fixed 6 (by decide) (by decide)).trans frame.floyd.one,
    fun i hi => (congrFun natural _).trans (frame.floyd.rows i hi)⟩,
    (fixed 24 (by decide) (by decide)).trans frame.labelBase,
    (fixed 37 (by decide) (by decide)).trans frame.bitBase,
    (fixed 33 (by decide) (by decide)).trans frame.zero,
    fun u v => (congrFun natural _).trans (frame.pairBits u v),
    frame.rowsBeforeLabels, frame.bitsBeforeLabels⟩

private def labelSweepMemory {n : ℕ} (step : Fin n → (ℕ → ℕ) → ℕ → ℕ)
    (count : ℕ) (memory : ℕ → ℕ) : ℕ → ℕ :=
  ((List.finRange n).take count).foldl (fun m i => step i m) memory

private theorem labelSweepMemory_succ {n : ℕ} (step : Fin n → (ℕ → ℕ) → ℕ → ℕ)
    (i : ℕ) (hi : i < n) (memory : ℕ → ℕ) :
    labelSweepMemory step (i + 1) memory = step ⟨i, hi⟩ (labelSweepMemory step i memory) := by
  have bound : i < (List.finRange n).length := by simpa using hi
  simp [labelSweepMemory, List.take_succ_eq_append_getElem bound, List.foldl_append]

private theorem labelSweepMemory_all {n : ℕ} (step : Fin n → (ℕ → ℕ) → ℕ → ℕ)
    (memory : ℕ → ℕ) :
    labelSweepMemory step n memory = (List.finRange n).foldl (fun m i => step i m) memory := by
  have whole : (List.finRange n).take n = List.finRange n :=
    List.take_of_length_le (by simp)
  simp only [labelSweepMemory, whole]

private structure LabelSweepState (n rows matrix labels bits control : ℕ)
    (required : Fin n → Fin n → Bool) (step : Fin n → (ℕ → ℕ) → ℕ → ℕ)
    (keep : (ℕ → ℕ) → Prop) (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr control = i
  frame : LabelPairFrame n rows matrix labels bits required s
  preserved : keep s.nr
  realMemory : s.rm = initial.rm
  realRegisters : s.rr = initial.rr
  natural : s.nm = labelSweepMemory step i initial.nm

private theorem labelSweep_correct {n rows matrix labels bits : ℕ}
    {required : Fin n → Fin n → Bool} {s : ArithmeticState}
    (frame : LabelPairFrame n rows matrix labels bits required s)
    (entry : s.pc = 0) (running : s.halted = false)
    (control : ℕ) (indexRegister : control = 34 ∨ control = 35)
    (code : List ArithmeticInstruction) (ticks : ℕ)
    (step : Fin n → (ℕ → ℕ) → ℕ → ℕ) (keep : (ℕ → ℕ) → Prop)
    (initialKeep : keep (Function.update s.nr control 0))
    (advance : ∀ (i : Fin n) (m : ArithmeticState),
      LabelPairFrame n rows matrix labels bits required m → m.pc = 0 → m.halted = false →
      m.nr control = i.val → keep m.nr →
      ∃ t, BlockRuns code ticks m t ∧ t.halted = false ∧
        LabelPairFrame n rows matrix labels bits required t ∧ t.nr control = i.val ∧
        keep (Function.update t.nr control (i.val + 1)) ∧
        t.rm = m.rm ∧ t.rr = m.rr ∧ t.nm = step i m.nm) :
    ∃ t, BlockRuns (countedLoopFromZero 6 control 5 code) (1 + (n * (ticks + 3) + 1)) s t ∧
      t.halted = false ∧ LabelPairFrame n rows matrix labels bits required t ∧ keep t.nr ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ t.nm = (List.finRange n).foldl (fun m i => step i m) s.nm := by
  let inv := LabelSweepState n rows matrix labels bits control required step keep s
  let first := {s with pc := 0, nr := Function.update s.nr control 0}
  have firstFrame : LabelPairFrame n rows matrix labels bits required first := by
    refine frame.copyControl (fun r row column => ?_) rfl
    change Function.update s.nr control 0 r = s.nr r
    rw [Function.update_of_ne (by omega)]
  have initial : inv 0 first :=
    ⟨rfl, running, by simp [first], firstFrame, initialKeep, rfl, rfl,
      by simp [first, labelSweepMemory]⟩
  have registers (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr control = i ∧ m.nr 5 = n :=
    ⟨hm.entry, hm.running, hm.index, hm.frame.floyd.dimension⟩
  have body (i : ℕ) (hi : i < n) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns code ticks m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr control (t.nr control + t.nr 6)} := by
    let vertex : Fin n := ⟨i, hi⟩
    obtain ⟨t, run, ready, current, position, same, rm, rr, nm⟩ :=
      advance vertex m hm.frame hm.entry hm.running hm.index hm.preserved
    let next := {t with pc := 0, nr := Function.update t.nr control (t.nr control + t.nr 6)}
    have nextFrame : LabelPairFrame n rows matrix labels bits required next := by
      refine current.copyControl (fun r row column => ?_) rfl
      change Function.update t.nr control (t.nr control + t.nr 6) r = t.nr r
      rw [Function.update_of_ne (by omega)]
    refine ⟨t, run, ready, rfl, ready, ?_, nextFrame, ?_, rm.trans hm.realMemory,
      rr.trans hm.realRegisters, ?_⟩
    · simp [next, position, current.floyd.one, vertex]
    · simpa [next, position, current.floyd.one, vertex] using same
    · change t.nm = _
      rw [nm, hm.natural, labelSweepMemory_succ step i hi]
  obtain ⟨last, complete, run⟩ :=
    countedLoopFromZero_correct 6 control 5 n ticks code inv entry running initial registers body
  let finish := relocateState 1 {last with pc := (countedLoop 6 control 5 code).length}
  have finalFrame : LabelPairFrame n rows matrix labels bits required finish :=
    complete.frame.copyControl (fun _ _ _ => rfl) rfl
  exact ⟨finish, run, complete.running, finalFrame, complete.preserved, complete.realMemory,
    complete.realRegisters, complete.natural.trans (labelSweepMemory_all step s.nm)⟩

def mergeLabelRowBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 35 5 mergeLabelPairBlock

def mergeLabelRowMemory {n : ℕ} (labels : ℕ) (required : Fin n → Fin n → Bool)
    (u : Fin n) (memory : ℕ → ℕ) : ℕ → ℕ :=
  (List.finRange n).foldl (fun m v => mergeLabelPairMemory labels (required u v) u v m) memory

theorem mergeLabelRowBlock_correct {n rows matrix labels bits : ℕ}
    {required : Fin n → Fin n → Bool} {s : ArithmeticState}
    (frame : LabelPairFrame n rows matrix labels bits required s)
    (entry : s.pc = 0) (running : s.halted = false) (u : Fin n) (row : s.nr 34 = u.val) :
    ∃ t, BlockRuns mergeLabelRowBlock (12 * n ^ 2 + 14 * n + 2) s t ∧ t.halted = false ∧
      LabelPairFrame n rows matrix labels bits required t ∧ t.nr 34 = u.val ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ t.nm = mergeLabelRowMemory labels required u s.nm := by
  let keep (nr : ℕ → ℕ) : Prop := nr 34 = u.val
  have start : keep (Function.update s.nr 35 0) := by simp [keep, row]
  obtain ⟨t, run, ready, finalFrame, rowAtEnd, rm, rr, nm⟩ :=
    labelSweep_correct frame entry running 35 (.inr rfl) mergeLabelPairBlock (12 * n + 11)
      (fun v m => mergeLabelPairMemory labels (required u v) u v m) keep start (by
        intro v m mFrame hasEntry mReady column mRow
        obtain ⟨next, executes, ready, nextFrame, newRow, newColumn, rm, rr, nm⟩ :=
          mergeLabelPairBlock_correct mFrame hasEntry mReady u v mRow column
        exact ⟨next, executes, ready, nextFrame, newColumn, by simp [keep, newRow], rm, rr, nm⟩)
  have total : 1 + (n * (12 * n + 11 + 3) + 1) = 12 * n ^ 2 + 14 * n + 2 := by ring
  exact ⟨t, by simpa only [mergeLabelRowBlock, total] using run, ready, finalFrame, rowAtEnd, rm, rr, nm⟩

def mergeAllLabelPairsBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 34 5 mergeLabelRowBlock

def mergeAllLabelPairsMemory {n : ℕ} (labels : ℕ) (required : Fin n → Fin n → Bool)
    (memory : ℕ → ℕ) : ℕ → ℕ :=
  (List.finRange n).foldl (fun m u => mergeLabelRowMemory labels required u m) memory

theorem mergeAllLabelPairsMemory_outside {n : ℕ} (labels : ℕ)
    (required : Fin n → Fin n → Bool) (memory : ℕ → ℕ) (k : ℕ)
    (outside : ¬(labels ≤ k ∧ k < labels + n)) :
    mergeAllLabelPairsMemory labels required memory k = memory k := by
  have oneRow (u : Fin n) (m : ℕ → ℕ) : mergeLabelRowMemory labels required u m k = m k := by
    unfold mergeLabelRowMemory
    generalize List.finRange n = columns
    induction columns generalizing m with
    | nil => rfl
    | cons v columns ih =>
      simp only [List.foldl_cons, ih, mergeLabelPairMemory, if_neg outside]
  unfold mergeAllLabelPairsMemory
  generalize List.finRange n = rows
  induction rows generalizing memory with
  | nil => rfl
  | cons u rows ih =>
    simp only [List.foldl_cons, ih, oneRow]

/-- Scan the dense required-pair matrix row by row, merging the classes
indicated by present pairs and preserving the input and other arrays. -/
theorem mergeAllLabelPairsBlock_correct {n rows matrix labels bits : ℕ}
    {required : Fin n → Fin n → Bool} {s : ArithmeticState}
    (frame : LabelPairFrame n rows matrix labels bits required s)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns mergeAllLabelPairsBlock (12 * n ^ 3 + 14 * n ^ 2 + 5 * n + 2) s t ∧
      t.halted = false ∧ LabelPairFrame n rows matrix labels bits required t ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ t.nm = mergeAllLabelPairsMemory labels required s.nm := by
  obtain ⟨t, run, ready, finalFrame, _, rm, rr, nm⟩ :=
    labelSweep_correct frame entry running 34 (.inl rfl) mergeLabelRowBlock (12 * n ^ 2 + 14 * n + 2)
      (fun u m => mergeLabelRowMemory labels required u m) (fun _ => True) trivial (by
        intro u m mFrame hasEntry mReady row _
        obtain ⟨next, executes, ready, nextFrame, newRow, rm, rr, nm⟩ :=
          mergeLabelRowBlock_correct mFrame hasEntry mReady u row
        exact ⟨next, executes, ready, nextFrame, newRow, trivial, rm, rr, nm⟩)
  have total : 1 + (n * (12 * n ^ 2 + 14 * n + 2 + 3) + 1) =
      12 * n ^ 3 + 14 * n ^ 2 + 5 * n + 2 := by ring
  exact ⟨t, by simpa only [mergeAllLabelPairsBlock, total] using run, ready, finalFrame, rm, rr, nm⟩

private theorem labelFold_view {n : ℕ} (labels : ℕ) (required : Fin n → Fin n → Bool)
    (pairs : List (Fin n × Fin n)) (memory : ℕ → ℕ) :
    (fun w : Fin n => (pairs.foldl (fun m p => mergeLabelPairMemory labels
      (required p.1 p.2) p.1 p.2 m) memory) (labels + w.val)) =
    (pairs.filter (fun p => required p.1 p.2)).foldl
      (fun a p => mergeComponentLabels a p.1 p.2) (fun w => memory (labels + w.val)) := by
  induction pairs generalizing memory with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.foldl_cons]
    rw [ih, mergeLabelPairMemory_labelView]
    cases present : required p.1 p.2 <;> simp [List.filter_cons, present]

theorem mergeAllLabelPairsMemory_sameComponent {I : Service} (labels : ℕ)
    (required : Fin I.graph.n → Fin I.graph.n → Bool) (memory : ℕ → ℕ)
    (exactPairs : ∀ u v, required u v = true ↔
      ∃ e ∈ I.links, I.graph.tail e = u ∧ I.graph.head e = v)
    (identity : ∀ v : Fin I.graph.n, memory (labels + v.val) = v.val)
    (u v : Fin I.graph.n) :
    let final := mergeAllLabelPairsMemory labels required memory
    final (labels + u.val) = final (labels + v.val) ↔ sameComponent I u v := by
  let all := (List.finRange I.graph.n).flatMap (fun x =>
    (List.finRange I.graph.n).map (fun y => (x, y)))
  let pairs := all.filter (fun p => required p.1 p.2)
  have allMembers (x y : Fin I.graph.n) : (x, y) ∈ all :=
    List.mem_flatMap.mpr ⟨x, List.mem_finRange x,
      List.mem_map.mpr ⟨y, List.mem_finRange y, rfl⟩⟩
  have covers (x y : Fin I.graph.n) : (x, y) ∈ pairs ↔
      ∃ e ∈ I.links, I.graph.tail e = x ∧ I.graph.head e = y := by
    simpa only [pairs, List.mem_filter, allMembers, true_and] using exactPairs x y
  have initialView : (fun w : Fin I.graph.n => memory (labels + w.val)) = Fin.val :=
    funext identity
  have finalView :
      (fun w : Fin I.graph.n => mergeAllLabelPairsMemory labels required memory (labels + w.val)) =
        labelComponentPairs pairs := by
    simpa only [mergeAllLabelPairsMemory, mergeLabelRowMemory, all, pairs, labelComponentPairs,
      List.foldl_flatMap, List.foldl_map, initialView] using labelFold_view labels required all memory
  change mergeAllLabelPairsMemory labels required memory (labels + u.val) =
    mergeAllLabelPairsMemory labels required memory (labels + v.val) ↔ sameComponent I u v
  rw [show _ = labelComponentPairs pairs u from congrFun finalView u,
    show _ = labelComponentPairs pairs v from congrFun finalView v]
  exact labelComponentPairs_sameComponent pairs covers u v

/-- With exact required-pair bits and identity labels, the machine's label
table represents precisely the required components. -/
theorem requiredLabelingBlock_correct {I : Service} {rows matrix labels bits : ℕ}
    {required : Fin I.graph.n → Fin I.graph.n → Bool} {s : ArithmeticState}
    (frame : LabelPairFrame I.graph.n rows matrix labels bits required s)
    (entry : s.pc = 0) (running : s.halted = false)
    (exactPairs : ∀ u v, required u v = true ↔
      ∃ e ∈ I.links, I.graph.tail e = u ∧ I.graph.head e = v)
    (identity : ∀ v : Fin I.graph.n, s.nm (labels + v.val) = v.val) :
    ∃ t, BlockRuns mergeAllLabelPairsBlock
      (12 * I.graph.n ^ 3 + 14 * I.graph.n ^ 2 + 5 * I.graph.n + 2) s t ∧
      t.halted = false ∧ LabelPairFrame I.graph.n rows matrix labels bits required t ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ u v : Fin I.graph.n, t.nm (labels + u.val) = t.nm (labels + v.val) ↔ sameComponent I u v) ∧
      ∀ k, ¬(labels ≤ k ∧ k < labels + I.graph.n) → t.nm k = s.nm k := by
  obtain ⟨t, run, ready, finalFrame, rm, rr, nm⟩ := mergeAllLabelPairsBlock_correct frame entry running
  refine ⟨t, run, ready, finalFrame, rm, rr, ?_, ?_⟩
  · intro u v
    rw [nm]
    exact mergeAllLabelPairsMemory_sameComponent labels required s.nm exactPairs identity u v
  · intro k outside
    rw [nm]
    exact mergeAllLabelPairsMemory_outside labels required s.nm k outside

end VehicleRoutingSurvey.Routing
end RppSource_RequiredLabelSweep

/-! runtime/RequiredLabelInit.lean -/
section RppSource_RequiredLabelInit
namespace VehicleRoutingSurvey.Routing

private def initLabelCell : List ArithmeticInstruction :=
  [.natAdd 28 24 7, .natStore 28 7]

private theorem initLabelCell_runs {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) :
    BlockRuns initLabelCell 2 s
      {s with
        pc := 2
        nr := Function.update s.nr 28 (s.nr 24 + s.nr 7)
        nm := Function.update s.nm (s.nr 24 + s.nr 7) (s.nr 7)} := by
  refine ⟨?_, ?_, rfl⟩
  · intro i hi
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl <;>
      simp [initLabelCell, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [initLabelCell, arithmeticStep, entry, running, Function.iterate_succ_apply']

def initIdentityLabelsBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 7 5 initLabelCell

private structure InitLabelState (initial : ArithmeticState) (labels i : ℕ)
    (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 7 = i
  fixed : ∀ r, r ≠ 7 → r ≠ 28 → s.nr r = initial.nr r
  realMemory : s.rm = initial.rm
  realRegisters : s.rr = initial.rr
  natural : ∀ k, s.nm k = if labels ≤ k ∧ k < labels + i then k - labels else initial.nm k

/-- Initialize every vertex's label to its own index, preserving the other arrays. -/
theorem initIdentityLabelsBlock_correct {n rows matrix labels bits : ℕ}
    {required : Fin n → Fin n → Bool} {s : ArithmeticState}
    (frame : LabelPairFrame n rows matrix labels bits required s)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns initIdentityLabelsBlock (5 * n + 2) s t ∧ t.halted = false ∧
      LabelPairFrame n rows matrix labels bits required t ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ k, t.nm k = if labels ≤ k ∧ k < labels + n then k - labels else s.nm k) ∧
      ∀ u : Fin n, t.nm (labels + u.val) = u.val := by
  let inv := InitLabelState s labels
  let first := {s with pc := 0, nr := Function.update s.nr 7 0}
  have initial : inv 0 first := by
    refine ⟨rfl, running, by simp [first], ?_, rfl, rfl, fun k => by simp [first]⟩
    intro r different _
    simp [first, Function.update_of_ne different]
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 5 = n :=
    ⟨hm.entry, hm.running, hm.index, (hm.fixed 5 (by decide) (by decide)).trans frame.floyd.dimension⟩
  have iterate (i : ℕ) (_ : i < n) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns initLabelCell 2 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)} := by
    let address := m.nr 24 + m.nr 7
    let t := {m with
      pc := 2
      nr := Function.update m.nr 28 address
      nm := Function.update m.nm address (m.nr 7)}
    have atLabel : address = labels + i := by
      simp [address, (hm.fixed 24 (by decide) (by decide)).trans frame.labelBase, hm.index]
    have one := (hm.fixed 6 (by decide) (by decide)).trans frame.floyd.one
    refine ⟨t, initLabelCell_runs hm.entry hm.running, hm.running, rfl, hm.running, ?_, ?_,
      hm.realMemory, hm.realRegisters, ?_⟩
    · simp [t, hm.index, one]
    · intro r different scratch
      simp [t, Function.update_of_ne different, Function.update_of_ne scratch, hm.fixed r different scratch]
    · intro k
      change Function.update m.nm address (m.nr 7) k = _
      rw [atLabel, hm.index]
      by_cases latest : k = labels + i
      · subst k
        rw [Function.update_self, if_pos (by omega)]
        simp
      · rw [Function.update_of_ne latest, hm.natural]
        have same : (labels ≤ k ∧ k < labels + (i + 1)) ↔ (labels ≤ k ∧ k < labels + i) := by omega
        simp only [same]
  obtain ⟨last, complete, run⟩ :=
    countedLoopFromZero_correct 6 7 5 n 2 initLabelCell inv entry running initial control iterate
  let finish := relocateState 1 {last with pc := (countedLoop 6 7 5 initLabelCell).length}
  have before (k : ℕ) (earlier : k < labels) : finish.nm k = s.nm k := by
    change last.nm k = _
    rw [complete.natural, if_neg (fun h => (not_le.mpr earlier) h.1)]
  have finalFrame : LabelPairFrame n rows matrix labels bits required finish :=
    ⟨⟨(complete.fixed 3 (by decide) (by decide)).trans frame.floyd.tableBase,
      (complete.fixed 4 (by decide) (by decide)).trans frame.floyd.matrixBase,
      (complete.fixed 5 (by decide) (by decide)).trans frame.floyd.dimension,
      (complete.fixed 6 (by decide) (by decide)).trans frame.floyd.one,
      fun i hi => (before _ ((Nat.add_lt_add_left hi _).trans_le frame.rowsBeforeLabels)).trans
        (frame.floyd.rows i hi)⟩,
      (complete.fixed 24 (by decide) (by decide)).trans frame.labelBase,
      (complete.fixed 37 (by decide) (by decide)).trans frame.bitBase,
      (complete.fixed 33 (by decide) (by decide)).trans frame.zero,
      fun u v => (before _ (frame.bitsBeforeLabels u v)).trans (frame.pairBits u v),
      frame.rowsBeforeLabels, frame.bitsBeforeLabels⟩
  have ticks : 1 + (n * (2 + 3) + 1) = 5 * n + 2 := by omega
  refine ⟨finish, by simpa only [initIdentityLabelsBlock, ticks] using run, complete.running,
    finalFrame, complete.realMemory, complete.realRegisters, complete.natural, fun u => ?_⟩
  change last.nm (labels + u.val) = u.val
  have inside : labels ≤ labels + u.val ∧ labels + u.val < labels + n :=
    ⟨Nat.le_add_right _ _, Nat.add_lt_add_left u.isLt _⟩
  simp [complete.natural, inside]

def labelRequiredComponentsBlock : List ArithmeticInstruction :=
  appendBlock initIdentityLabelsBlock mergeAllLabelPairsBlock

theorem labelRequiredComponentsBlock_correct {I : Service} {rows matrix labels bits : ℕ}
    {required : Fin I.graph.n → Fin I.graph.n → Bool} {s : ArithmeticState}
    (frame : LabelPairFrame I.graph.n rows matrix labels bits required s)
    (entry : s.pc = 0) (running : s.halted = false)
    (exactPairs : ∀ u v, required u v = true ↔
      ∃ e ∈ I.links, I.graph.tail e = u ∧ I.graph.head e = v) :
    ∃ t, BlockRuns labelRequiredComponentsBlock
      (12 * I.graph.n ^ 3 + 14 * I.graph.n ^ 2 + 10 * I.graph.n + 4) s t ∧
      t.halted = false ∧ LabelPairFrame I.graph.n rows matrix labels bits required t ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ u v : Fin I.graph.n, t.nm (labels + u.val) = t.nm (labels + v.val) ↔ sameComponent I u v) ∧
      ∀ k, ¬(labels ≤ k ∧ k < labels + I.graph.n) → t.nm k = s.nm k := by
  obtain ⟨initial, init, initReady, f, initReal, initRegisters, initNatural, identity⟩ :=
    initIdentityLabelsBlock_correct frame entry running
  let ready := {initial with pc := 0}
  have readyFrame : LabelPairFrame I.graph.n rows matrix labels bits required ready :=
    ⟨⟨f.floyd.tableBase, f.floyd.matrixBase, f.floyd.dimension, f.floyd.one, f.floyd.rows⟩,
      f.labelBase, f.bitBase, f.zero, f.pairBits, f.rowsBeforeLabels, f.bitsBeforeLabels⟩
  obtain ⟨merged, scan, readyAtEnd, last, mergedReal, mergedRegisters, related, mergedNatural⟩ :=
    requiredLabelingBlock_correct readyFrame rfl initReady exactPairs identity
  let finish := relocateState initIdentityLabelsBlock.length merged
  have result := init.append scan
  have next : LabelPairFrame I.graph.n rows matrix labels bits required finish :=
    ⟨⟨last.floyd.tableBase, last.floyd.matrixBase, last.floyd.dimension, last.floyd.one, last.floyd.rows⟩,
      last.labelBase, last.bitBase, last.zero, last.pairBits, last.rowsBeforeLabels, last.bitsBeforeLabels⟩
  have ticks : (5 * I.graph.n + 2) + (12 * I.graph.n ^ 3 + 14 * I.graph.n ^ 2 + 5 * I.graph.n + 2) =
      12 * I.graph.n ^ 3 + 14 * I.graph.n ^ 2 + 10 * I.graph.n + 4 := by ring
  refine ⟨finish, by simpa only [labelRequiredComponentsBlock, ticks] using result,
    readyAtEnd, next, mergedReal.trans initReal, mergedRegisters.trans initRegisters, related, ?_⟩
  intro k outside
  exact (mergedNatural k outside).trans (by rw [initNatural, if_neg outside])

end VehicleRoutingSurvey.Routing
end RppSource_RequiredLabelInit

/-! runtime/RequiredPreprocessing.lean -/
section RppSource_RequiredPreprocessing
namespace VehicleRoutingSurvey.Routing

def requiredComponentPreprocessingBlock : List ArithmeticInstruction :=
  appendBlock requiredBitScanBlock labelRequiredComponentsBlock

/-- Read the required input links, seed the vertex labels, and classify
all required components. The reserved pair-bit area initially contains zeros. -/
theorem requiredComponentPreprocessingBlock_correct {I : Service}
    {rows matrix bits labels : ℕ} {s : ArithmeticState}
    (frame : RequiredBitFrame I rows matrix bits s) (entry : s.pc = 0) (running : s.halted = false)
    (cursor : s.nr 9 = 2) (labelBase : s.nr 24 = labels)
    (labelsAfterBits : bits ≤ labels)
    (rowsBeforeLabels : rows + I.graph.n ≤ labels)
    (bitsBeforeLabels : ∀ u v : Fin I.graph.n, bits + I.graph.n * u.val + v.val < labels)
    (zeros : ∀ u v : Fin I.graph.n, s.nm (bits + I.graph.n * u.val + v.val) = 0) :
    ∃ t, BlockRuns requiredComponentPreprocessingBlock
      (12 * I.graph.n ^ 3 + 14 * I.graph.n ^ 2 + 10 * I.graph.n + 15 * I.graph.q + 6) s t ∧
      t.halted = false ∧ LabelPairFrame I.graph.n rows matrix labels bits (requiredPairFlag I) t ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ k < bits, t.nm k = s.nm k) ∧
      ∀ u v : Fin I.graph.n, t.nm (labels + u.val) = t.nm (labels + v.val) ↔ sameComponent I u v := by
  obtain ⟨flagged, flagRun, flagReady, f, flagRm, flagRr, flagMemory, flagLabelBase⟩ :=
    requiredBitScanBlock_correct frame entry running cursor
  let ready := {flagged with pc := 0}
  have initial : LabelPairFrame I.graph.n rows matrix labels bits (requiredPairFlag I) ready := by
    refine ⟨⟨f.floyd.tableBase, f.floyd.matrixBase, f.floyd.dimension, f.floyd.one, f.floyd.rows⟩,
      flagLabelBase.trans labelBase, f.bitBase, f.zero, ?_, rowsBeforeLabels, bitsBeforeLabels⟩
    intro u v
    change flagged.nm _ = _
    rw [flagMemory]
    exact requiredBitScanMemory_exact bits s.nm zeros u v
  obtain ⟨merged, mergeRun, mergeReady, g, mergeRm, mergeRr, related, mergeMemory⟩ :=
    labelRequiredComponentsBlock_correct initial rfl flagReady (requiredPairFlag_exact I)
  let finish := relocateState requiredBitScanBlock.length merged
  have finalFrame : LabelPairFrame I.graph.n rows matrix labels bits (requiredPairFlag I) finish :=
    ⟨⟨g.floyd.tableBase, g.floyd.matrixBase, g.floyd.dimension, g.floyd.one, g.floyd.rows⟩,
      g.labelBase, g.bitBase, g.zero, g.pairBits, g.rowsBeforeLabels, g.bitsBeforeLabels⟩
  have total : (15 * I.graph.q + 2) + (12 * I.graph.n ^ 3 + 14 * I.graph.n ^ 2 + 10 * I.graph.n + 4) =
       12 * I.graph.n ^ 3 + 14 * I.graph.n ^ 2 + 10 * I.graph.n + 15 * I.graph.q + 6 := by ring
  refine ⟨finish, by simpa only [requiredComponentPreprocessingBlock, total] using flagRun.append mergeRun,
    mergeReady, finalFrame, mergeRm.trans flagRm, mergeRr.trans flagRr, ?_, related⟩
  intro k hk
  have same := mergeMemory k (fun inLabels => (not_le.mpr (hk.trans_le labelsAfterBits)) inLabels.1)
  change merged.nm k = flagged.nm k at same
  change merged.nm k = s.nm k
  rw [same, flagMemory]
  exact requiredBitScanMemory_before I.graph.q s.nm hk

end VehicleRoutingSurvey.Routing
end RppSource_RequiredPreprocessing

/-! runtime/RequiredBitInit.lean -/
section RppSource_RequiredBitInit
namespace VehicleRoutingSurvey.Routing

private def clearRequiredBit : List ArithmeticInstruction :=
  [.natAdd 38 37 7, .natStore 38 33]

private theorem clearRequiredBit_runs {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) :
    BlockRuns clearRequiredBit 2 s
      {s with
        pc := 2
        nr := Function.update s.nr 38 (s.nr 37 + s.nr 7)
        nm := Function.update s.nm (s.nr 37 + s.nr 7) (s.nr 33)} := by
  refine ⟨?_, ?_, rfl⟩
  · intro i hi
    have two : i = 0 ∨ i = 1 := by omega
    rcases two with rfl | rfl <;>
      simp [clearRequiredBit, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [clearRequiredBit, arithmeticStep, entry, running, Function.iterate_succ_apply']

def clearRequiredBitsBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 7 23 clearRequiredBit

private structure ClearRequiredBitsState (initial : ArithmeticState) (base i : ℕ)
    (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 7 = i
  fixed : ∀ r, r ≠ 7 → r ≠ 38 → s.nr r = initial.nr r
  rm : s.rm = initial.rm
  rr : s.rr = initial.rr
  memory : ∀ k, s.nm k = if base ≤ k ∧ k < base + i then 0 else initial.nm k

theorem clearRequiredBitsBlock_correct {s : ArithmeticState} {base count : ℕ}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (zero : s.nr 33 = 0) (baseAt : s.nr 37 = base) (countAt : s.nr 23 = count) :
    ∃ t, BlockRuns clearRequiredBitsBlock (5 * count + 2) s t ∧ t.halted = false ∧
      (∀ r, r ≠ 7 → r ≠ 38 → t.nr r = s.nr r) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ k, t.nm k = if base ≤ k ∧ k < base + count then 0 else s.nm k := by
  let inv := ClearRequiredBitsState s base
  let first := {s with pc := 0, nr := Function.update s.nr 7 0}
  have initial : inv 0 first := by
    refine ⟨rfl, running, by simp [first], ?_, rfl, rfl, fun k => by simp [first]⟩
    intro r stable _
    simp [first, Function.update_of_ne stable]
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 23 = count :=
    ⟨hm.entry, hm.running, hm.index, (hm.fixed 23 (by decide) (by decide)).trans countAt⟩
  have step (i : ℕ) (_ : i < count) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns clearRequiredBit 2 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)} := by
    let address := m.nr 37 + m.nr 7
    let t := {m with
      pc := 2
      nr := Function.update m.nr 38 address
      nm := Function.update m.nm address (m.nr 33)}
    have cell : address = base + i := by
      simp [address, hm.index, (hm.fixed 37 (by decide) (by decide)).trans baseAt]
    have oneAt := (hm.fixed 6 (by decide) (by decide)).trans one
    have zeroAt := (hm.fixed 33 (by decide) (by decide)).trans zero
    refine ⟨t, clearRequiredBit_runs hm.entry hm.running, hm.running, rfl, hm.running, ?_, ?_,
      hm.rm, hm.rr, ?_⟩
    · simp [t, hm.index, oneAt]
    · intro r first second
      simp [t, Function.update_of_ne first, Function.update_of_ne second, hm.fixed r first second]
    · intro k
      change Function.update m.nm address (m.nr 33) k = _
      rw [cell, zeroAt]
      by_cases last : k = base + i
      · subst k
        rw [Function.update_self, if_pos (by omega)]
      · rw [Function.update_of_ne last, hm.memory]
        have same : (base ≤ k ∧ k < base + (i + 1)) ↔ (base ≤ k ∧ k < base + i) := by omega
        simp only [same]
  obtain ⟨last, complete, run⟩ :=
    countedLoopFromZero_correct 6 7 23 count 2 clearRequiredBit inv entry running initial control step
  let finish := relocateState 1 {last with pc := (countedLoop 6 7 23 clearRequiredBit).length}
  have ticks : 1 + (count * (2 + 3) + 1) = 5 * count + 2 := by omega
  exact ⟨finish, by simpa only [clearRequiredBitsBlock, ticks] using run, complete.running,
    complete.fixed, complete.rm, complete.rr, complete.memory⟩

/-- Reserve pair bits and labels immediately after the next-edge rows.
The last row offset gives the matrix size without a multiplication opcode. -/
def requiredComponentLayoutBlock : List ArithmeticInstruction :=
  [.natSub 38 5 6, .natAdd 38 3 38, .natLoad 23 38, .natAdd 23 23 5,
    .natAdd 37 26 23, .natAdd 24 37 23, .natLoad 8 6, .natConst 9 2, .natConst 33 0]

private def requiredComponentLayoutState (s : ArithmeticState) : ArithmeticState :=
  let previous := s.nr 5 - s.nr 6
  let lastRow := s.nr 3 + previous
  let cells := s.nm lastRow + s.nr 5
  let bits := s.nr 26 + cells
  let labels := bits + cells
  let nr := Function.update (Function.update s.nr 38 lastRow) 23 cells
  let nr := Function.update (Function.update nr 37 bits) 24 labels
  let nr := Function.update (Function.update (Function.update nr 8 (s.nm (s.nr 6))) 9 2) 33 0
  {s with pc := 9, nr}

theorem requiredComponentLayoutBlock_correct {s : ArithmeticState} {n rows matrix next : ℕ}
    (frame : FloydFrame n rows matrix s) (positive : 0 < n) (nextAt : s.nr 26 = next)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns requiredComponentLayoutBlock 9 s t ∧ t.halted = false ∧
      FloydFrame n rows matrix t ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      t.nr 23 = n ^ 2 ∧ t.nr 37 = next + n ^ 2 ∧ t.nr 24 = next + n ^ 2 + n ^ 2 ∧
      t.nr 8 = s.nm 1 ∧ t.nr 9 = 2 ∧ t.nr 33 = 0 := by
  let t := requiredComponentLayoutState s
  have lastIndex : n - 1 < n := by omega
  have successor : (n - 1).succ = n := by omega
  have count : s.nm (s.nr 3 + (s.nr 5 - 1)) + s.nr 5 = n ^ 2 := by
    rw [frame.tableBase, frame.dimension, frame.rows _ lastIndex, pow_two, ← Nat.mul_succ, successor]
  have run : BlockRuns requiredComponentLayoutBlock 9 s t := by
    refine ⟨?_, ?_, rfl⟩
    · intro i hi
      interval_cases i <;> simp [requiredComponentLayoutBlock, arithmeticStep, entry, running,
        Function.iterate_succ_apply']
    · simp [t, requiredComponentLayoutState, requiredComponentLayoutBlock, arithmeticStep, entry,
        running, Function.iterate_succ_apply', Function.update_idem]
  have fixed : FixedFloydRegisters 7 s t := by
    intro r _ below
    simp [t, requiredComponentLayoutState, Function.update_of_ne (show r ≠ 38 by omega),
      Function.update_of_ne (show r ≠ 23 by omega), Function.update_of_ne (show r ≠ 37 by omega),
      Function.update_of_ne (show r ≠ 24 by omega), Function.update_of_ne (show r ≠ 8 by omega),
      Function.update_of_ne (show r ≠ 9 by omega), Function.update_of_ne (show r ≠ 33 by omega)]
  refine ⟨t, run, running, frame.preserved fixed rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [t, requiredComponentLayoutState, count, nextAt, frame.one]

def requiredComponentsAfterPathsBlock : List ArithmeticInstruction :=
  appendBlock requiredComponentLayoutBlock
    (appendBlock clearRequiredBitsBlock requiredComponentPreprocessingBlock)

private theorem rowMajor_lt_square {n : ℕ} (u v : Fin n) :
    n * u.val + v.val < n ^ 2 := by
  rw [pow_two]
  calc
    _ < n * (u.val + 1) := by rw [Nat.mul_succ]; exact Nat.add_lt_add_left v.isLt _
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt u.isLt)

/-- Classify required components after the shortest-path stage. All
natural cells below the new pair-bit area, including the entire next-edge
matrix, remain available. -/
theorem requiredComponentsAfterPathsBlock_correct {I : Service} {rows matrix next : ℕ}
    {s : ArithmeticState} (frame : FloydFrame I.graph.n rows matrix s)
    (positive : 0 < I.graph.n) (cursor : s.nr 26 = next)
    (input : ∀ k < 2 + 3 * I.graph.q, s.nm k = (ruralNatInput I)[k]?.getD 0)
    (inputBefore : 2 + 3 * I.graph.q ≤ next) (rowsBefore : rows + I.graph.n ≤ next)
    (entry : s.pc = 0) (running : s.halted = false) :
    let bits := next + I.graph.n ^ 2
    let labels := bits + I.graph.n ^ 2
    ∃ t, BlockRuns requiredComponentsAfterPathsBlock
      (12 * I.graph.n ^ 3 + 19 * I.graph.n ^ 2 + 10 * I.graph.n + 15 * I.graph.q + 17) s t ∧
      t.halted = false ∧ LabelPairFrame I.graph.n rows matrix labels bits (requiredPairFlag I) t ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ (∀ k < bits, t.nm k = s.nm k) ∧
      ∀ u v : Fin I.graph.n, t.nm (labels + u.val) = t.nm (labels + v.val) ↔ sameComponent I u v := by
  intro bits labels
  have rawCount : s.nm 1 = I.graph.q := by
    rw [input _ (by omega)]
    simp [ruralNatInput]
  obtain ⟨layout, layoutRun, layoutReady, layoutFrame, layoutNm, layoutRm, layoutRr,
    countAt, bitsAt, labelsAt, qAt, cursorAt, zeroAt⟩ :=
    requiredComponentLayoutBlock_correct frame positive cursor entry running
  let clearStart := {layout with pc := 0}
  obtain ⟨cleared, clearRun, clearReady, fixed, clearRm, clearRr, clearMemory⟩ :=
    clearRequiredBitsBlock_correct (s := clearStart) rfl layoutReady layoutFrame.one zeroAt bitsAt countAt
  have bitsAfterInput : 2 + 3 * I.graph.q ≤ bits := inputBefore.trans (Nat.le_add_right _ _)
  have bitsAfterRows : rows + I.graph.n ≤ bits := rowsBefore.trans (Nat.le_add_right _ _)
  have kept (k : ℕ) (hk : k < bits) : cleared.nm k = s.nm k := by
    rw [clearMemory, if_neg (fun written => (not_le.mpr hk) written.1)]
    exact congrFun layoutNm k
  let scanStart := {cleared with pc := 0}
  have scanFrame : RequiredBitFrame I rows matrix bits scanStart :=
    ⟨⟨(fixed 3 (by decide) (by decide)).trans layoutFrame.tableBase,
      (fixed 4 (by decide) (by decide)).trans layoutFrame.matrixBase,
      (fixed 5 (by decide) (by decide)).trans layoutFrame.dimension,
      (fixed 6 (by decide) (by decide)).trans layoutFrame.one,
      fun i hi => (kept _ ((Nat.add_lt_add_left hi _).trans_le bitsAfterRows)).trans
        ((congrFun layoutNm _).symm.trans (layoutFrame.rows i hi))⟩,
      (fixed 8 (by decide) (by decide)).trans (qAt.trans rawCount),
      (fixed 37 (by decide) (by decide)).trans bitsAt,
      (fixed 33 (by decide) (by decide)).trans zeroAt,
      fun k hk => (kept _ (hk.trans_le bitsAfterInput)).trans (input k hk),
      bitsAfterInput, bitsAfterRows⟩
  have initialBits (u v : Fin I.graph.n) : scanStart.nm (bits + I.graph.n * u.val + v.val) = 0 := by
    change cleared.nm _ = 0
    rw [clearMemory, if_pos]
    have bounded := rowMajor_lt_square u v
    omega
  have labelsAfterBits : bits ≤ labels := Nat.le_add_right _ _
  have pairArea (u v : Fin I.graph.n) : bits + I.graph.n * u.val + v.val < labels := by
    have bounded := rowMajor_lt_square u v
    change bits + I.graph.n * u.val + v.val < bits + I.graph.n ^ 2
    omega
  obtain ⟨merged, mergeRun, mergeReady, f, mergeRm, mergeRr, low, sameComponent⟩ :=
    requiredComponentPreprocessingBlock_correct scanFrame rfl clearReady
      ((fixed 9 (by decide) (by decide)).trans cursorAt) ((fixed 24 (by decide) (by decide)).trans labelsAt)
      labelsAfterBits (bitsAfterRows.trans labelsAfterBits) pairArea initialBits
  let finish := relocateState requiredComponentLayoutBlock.length
    (relocateState clearRequiredBitsBlock.length merged)
  have finalFrame : LabelPairFrame I.graph.n rows matrix labels bits (requiredPairFlag I) finish :=
    ⟨⟨f.floyd.tableBase, f.floyd.matrixBase, f.floyd.dimension, f.floyd.one, f.floyd.rows⟩,
      f.labelBase, f.bitBase, f.zero, f.pairBits, f.rowsBeforeLabels, f.bitsBeforeLabels⟩
  have total : 9 + ((5 * I.graph.n ^ 2 + 2) +
      (12 * I.graph.n ^ 3 + 14 * I.graph.n ^ 2 + 10 * I.graph.n + 15 * I.graph.q + 6)) =
      12 * I.graph.n ^ 3 + 19 * I.graph.n ^ 2 + 10 * I.graph.n + 15 * I.graph.q + 17 := by ring
  exact ⟨finish, by simpa only [requiredComponentsAfterPathsBlock, total] using
      layoutRun.append (clearRun.append mergeRun), mergeReady, finalFrame,
    (mergeRm.trans clearRm).trans layoutRm, (mergeRr.trans clearRr).trans layoutRr,
    fun k hk => (low k hk).trans (kept k hk), sameComponent⟩

end VehicleRoutingSurvey.Routing
end RppSource_RequiredBitInit

/-! runtime/PrimSupport.lean -/
section RppSource_PrimSupport
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Collect one required link's endpoints and remember its tail as a
possible starting vertex. Both branches use twelve instructions. -/
private def primSupportCell : List ArithmeticInstruction :=
  [.natLoad 11 9, .natAdd 9 9 6, .natLoad 12 9, .natAdd 9 9 6, .natLoad 13 9, .natAdd 9 9 6,
    .natBranch 13 33 7 12, .jump 8, .jump 9, .jump 10, .jump 11, .jump 17,
    .natAdd 44 40 11, .natStore 44 6, .natAdd 44 40 12, .natStore 44 6, .natAdd 45 11 33]

private def primSupportCellState (s : ArithmeticState) : ArithmeticState :=
  let input := s.nr 9
  let one := s.nr 6
  let u := s.nm input
  let v := s.nm (input + one)
  let flag := s.nm (input + one + one)
  let nr := Function.update s.nr 11 u
  let nr := Function.update nr 9 (input + one)
  let nr := Function.update nr 12 v
  let nr := Function.update nr 9 (input + one + one)
  let nr := Function.update nr 13 flag
  let nr := Function.update nr 9 (input + one + one + one)
  let uCell := s.nr 40 + u
  let vCell := s.nr 40 + v
  if flag ≤ s.nr 33 then {s with pc := 17, nr := nr}
  else
    {s with
      pc := 17
      nr := Function.update (Function.update nr 44 vCell) 45 (u + s.nr 33)
      nm := Function.update (Function.update s.nm uCell one) vCell one}

private theorem primSupportCell_runs {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) :
    BlockRuns primSupportCell 12 s (primSupportCellState s) := by
  by_cases skip : s.nm (s.nr 9 + s.nr 6 + s.nr 6) ≤ s.nr 33
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      interval_cases i <;> simp [primSupportCell, arithmeticStep, entry, running,
        Function.iterate_succ_apply', skip]
    · simp [primSupportCellState, primSupportCell, arithmeticStep, entry, running,
        Function.iterate_succ_apply', Function.update_idem, skip]
    · simp [primSupportCellState, primSupportCell, skip]

structure PrimSupportFrame (I : Service) (rows matrix support : ℕ) (s : ArithmeticState) : Prop where
  floyd : FloydFrame I.graph.n rows matrix s
  count : s.nr 8 = I.graph.q
  base : s.nr 40 = support
  zero : s.nr 33 = 0
  input : ∀ k < 2 + 3 * I.graph.q, s.nm k = (ruralNatInput I)[k]?.getD 0
  inputBelow : 2 + 3 * I.graph.q ≤ support
  rowsBelow : rows + I.graph.n ≤ support

def assignRequiredSupport (I : Service) (support : ℕ) (e : Fin I.graph.q)
    (memory : ℕ → ℕ) : ℕ → ℕ :=
  if e ∈ I.links then
    Function.update (Function.update memory (support + (I.graph.tail e).val) 1)
      (support + (I.graph.head e).val) 1
  else memory

def rememberRequiredTail (I : Service) (e : Fin I.graph.q) (prior : ℕ) : ℕ :=
  if e ∈ I.links then (I.graph.tail e).val else prior

private theorem primSupportCell_correct {I : Service} {rows matrix support : ℕ} {s : ArithmeticState}
    (frame : PrimSupportFrame I rows matrix support s) (entry : s.pc = 0) (running : s.halted = false)
    (e : Fin I.graph.q) (cursor : s.nr 9 = 2 + 3 * e.val) :
    ∃ t, BlockRuns primSupportCell 12 s t ∧ t.halted = false ∧
      (∀ r, r ∉ ([9, 11, 12, 13, 44, 45] : List ℕ) → t.nr r = s.nr r) ∧
      t.nr 9 = 2 + 3 * (e.val + 1) ∧ t.nr 45 = rememberRequiredTail I e (s.nr 45) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ t.nm = assignRequiredSupport I support e s.nm := by
  let t := primSupportCellState s
  have cell (j : ℕ) (inRecord : j < 3) :
      s.nm (2 + 3 * e.val + j) =
        ([(I.graph.tail e).val, (I.graph.head e).val, if e ∈ I.links then 1 else 0][j]?).getD 0 := by
    have inInput := e.isLt
    rw [frame.input _ (by omega), ruralNatInput_link_record I e inRecord]
  have tail : s.nm (s.nr 9) = (I.graph.tail e).val := by simpa [cursor] using cell 0 (by decide)
  have head : s.nm (s.nr 9 + 1) = (I.graph.head e).val := by simpa [cursor] using cell 1 (by decide)
  have flag : s.nm (s.nr 9 + 1 + 1) = if e ∈ I.links then 1 else 0 := by
    simpa [cursor, Nat.add_assoc] using cell 2 (by decide)
  have run := primSupportCell_runs entry running
  refine ⟨t, run, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases needed : e ∈ I.links <;> simp [t, primSupportCellState, frame.floyd.one, frame.zero, flag, needed, running]
  · intro r untouched
    have different (j : ℕ) (written : j ∈ ([9, 11, 12, 13, 44, 45] : List ℕ)) : r ≠ j :=
      fun equal => untouched (equal.symm ▸ written)
    by_cases needed : e ∈ I.links <;>
      simp [t, primSupportCellState, frame.floyd.one, frame.zero, flag, needed,
        Function.update_of_ne (different 9 (by decide)), Function.update_of_ne (different 11 (by decide)),
        Function.update_of_ne (different 12 (by decide)), Function.update_of_ne (different 13 (by decide)),
        Function.update_of_ne (different 44 (by decide)), Function.update_of_ne (different 45 (by decide))]
  · by_cases needed : e ∈ I.links <;>
      simp [t, primSupportCellState, frame.floyd.one, frame.zero, flag, needed] <;> omega
  · by_cases needed : e ∈ I.links <;>
      simp [t, primSupportCellState, frame.floyd.one, frame.zero, flag, needed, tail, rememberRequiredTail]
  · by_cases needed : e ∈ I.links <;> simp [t, primSupportCellState, frame.floyd.one, frame.zero, flag, needed]
  · by_cases needed : e ∈ I.links <;> simp [t, primSupportCellState, frame.floyd.one, frame.zero, flag, needed]
  · by_cases needed : e ∈ I.links <;>
      simp [t, primSupportCellState, frame.floyd.one, frame.zero, flag, needed, head, tail,
        frame.base, assignRequiredSupport]

private theorem assignRequiredSupport_outside {I : Service} (support : ℕ) (e : Fin I.graph.q)
    (memory : ℕ → ℕ) (k : ℕ) (outside : ¬(support ≤ k ∧ k < support + I.graph.n)) :
    assignRequiredSupport I support e memory k = memory k := by
  have tail : k ≠ support + (I.graph.tail e).val := by
    intro equal
    apply outside
    rw [equal]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (I.graph.tail e).isLt _⟩
  have head : k ≠ support + (I.graph.head e).val := by
    intro equal
    apply outside
    rw [equal]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (I.graph.head e).isLt _⟩
  by_cases needed : e ∈ I.links <;> simp [assignRequiredSupport, needed, Function.update_of_ne tail,
    Function.update_of_ne head]

private theorem assignRequiredSupport_at {I : Service} (support : ℕ) (e : Fin I.graph.q)
    (memory : ℕ → ℕ) (v : Fin I.graph.n) :
    assignRequiredSupport I support e memory (support + v.val) =
      if e ∈ I.links ∧ (I.graph.tail e = v ∨ I.graph.head e = v) then 1 else memory (support + v.val) := by
  by_cases needed : e ∈ I.links
  · by_cases tail : I.graph.tail e = v
    · rw [if_pos ⟨needed, Or.inl tail⟩]
      by_cases head : I.graph.head e = v
      · simp [assignRequiredSupport, needed, head]
      · have different : support + v.val ≠ support + (I.graph.head e).val :=
          fun h => head (Fin.ext (Nat.add_left_cancel h).symm)
        simp [assignRequiredSupport, needed, tail, Function.update_of_ne different]
    · by_cases head : I.graph.head e = v
      · rw [if_pos ⟨needed, Or.inr head⟩]
        simp [assignRequiredSupport, needed, head]
      · have notTail : support + v.val ≠ support + (I.graph.tail e).val :=
          fun h => tail (Fin.ext (Nat.add_left_cancel h).symm)
        have notHead : support + v.val ≠ support + (I.graph.head e).val :=
          fun h => head (Fin.ext (Nat.add_left_cancel h).symm)
        simp [assignRequiredSupport, needed, tail, head, Function.update_of_ne notTail, Function.update_of_ne notHead]
  · simp [assignRequiredSupport, needed]

private def SupportFromPrefix (I : Service) (i : ℕ) (v : Fin I.graph.n) : Prop :=
  ∃ e : Fin I.graph.q, e.val < i ∧ e ∈ I.links ∧ (I.graph.tail e = v ∨ I.graph.head e = v)

private theorem supportFromPrefix_next {I : Service} (i : ℕ) (bound : i < I.graph.q) (v : Fin I.graph.n) :
    SupportFromPrefix I (i + 1) v ↔ SupportFromPrefix I i v ∨
      (⟨i, bound⟩ : Fin I.graph.q) ∈ I.links ∧
        (I.graph.tail ⟨i, bound⟩ = v ∨ I.graph.head ⟨i, bound⟩ = v) := by
  constructor
  · rintro ⟨e, position, needed, ends⟩
    by_cases same : e.val = i
    · have equal : e = ⟨i, bound⟩ := Fin.ext same
      subst e
      exact Or.inr ⟨needed, ends⟩
    · exact Or.inl ⟨e, by omega, needed, ends⟩
  · rintro (⟨e, earlier, needed, ends⟩ | ⟨needed, ends⟩)
    · exact ⟨e, earlier.trans (Nat.lt_succ_self _), needed, ends⟩
    · exact ⟨⟨i, bound⟩, Nat.lt_succ_self _, needed, ends⟩

private theorem supportFromPrefix_all {I : Service} (v : Fin I.graph.n) :
    SupportFromPrefix I I.graph.q v ↔ v ∈ requiredVertices I := by
  constructor
  · rintro ⟨e, _, needed, rfl | rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ needed)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ needed)
  · intro required
    rcases Finset.mem_union.mp required with tail | head
    · obtain ⟨e, needed, position⟩ := Finset.mem_image.mp tail
      exact ⟨e, e.isLt, needed, Or.inl position⟩
    · obtain ⟨e, needed, position⟩ := Finset.mem_image.mp head
      exact ⟨e, e.isLt, needed, Or.inr position⟩

def primSupportScanBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 7 8 primSupportCell

private abbrev PrimSupportRegisters (s t : ArithmeticState) : Prop :=
  ∀ r, r ∉ ([7, 9, 11, 12, 13, 44, 45] : List ℕ) → t.nr r = s.nr r

open Classical in
private structure PrimSupportScanState (I : Service) (rows matrix support i : ℕ)
    (initial s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 7 = i
  cursor : s.nr 9 = 2 + 3 * i
  frame : PrimSupportFrame I rows matrix support s
  fixed : PrimSupportRegisters initial s
  rm : s.rm = initial.rm
  rr : s.rr = initial.rr
  outside : ∀ k, ¬(support ≤ k ∧ k < support + I.graph.n) → s.nm k = initial.nm k
  bits : ∀ v : Fin I.graph.n, s.nm (support + v.val) = if SupportFromPrefix I i v then 1 else 0
  root : (s.nr 45 = I.graph.n ∧ ∀ e : Fin I.graph.q, e.val < i → e ∉ I.links) ∨
    ∃ e : Fin I.graph.q, e.val < i ∧ e ∈ I.links ∧ s.nr 45 = (I.graph.tail e).val

open Classical in
/-- Build support flags and choose a starting vertex using a linear input scan. -/
theorem primSupportScanBlock_correct {I : Service} {rows matrix support : ℕ} {s : ArithmeticState}
    (frame : PrimSupportFrame I rows matrix support s)
    (entry : s.pc = 0) (running : s.halted = false) (cursor : s.nr 9 = 2)
    (noRoot : s.nr 45 = I.graph.n) (zeros : ∀ v : Fin I.graph.n, s.nm (support + v.val) = 0)
    (nonempty : I.links.Nonempty) :
    ∃ (t : ArithmeticState) (root : Fin I.graph.n), BlockRuns primSupportScanBlock (15 * I.graph.q + 2) s t ∧
      t.halted = false ∧ PrimSupportFrame I rows matrix support t ∧
      PrimSupportRegisters s t ∧ t.nr 45 = root.val ∧ root ∈ requiredVertices I ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ k, ¬(support ≤ k ∧ k < support + I.graph.n) → t.nm k = s.nm k) ∧
      ∀ v : Fin I.graph.n, t.nm (support + v.val) = if v ∈ requiredVertices I then 1 else 0 := by
  let inv (i : ℕ) (m : ArithmeticState) := PrimSupportScanState I rows matrix support i s m
  let first := {s with pc := 0, nr := Function.update s.nr 7 0}
  have firstFrame : PrimSupportFrame I rows matrix support first := by
    refine ⟨⟨?_, ?_, ?_, ?_, frame.floyd.rows⟩, ?_, ?_, ?_, frame.input, frame.inputBelow, frame.rowsBelow⟩
    all_goals simp [first, frame.floyd.tableBase, frame.floyd.matrixBase, frame.floyd.dimension,
      frame.floyd.one, frame.count, frame.base, frame.zero]
  have initial : inv 0 first := by
    refine ⟨rfl, running, by simp [first], by simpa [first] using cursor, firstFrame, ?_,
      rfl, rfl, fun _ _ => rfl, ?_, Or.inl ⟨noRoot, fun e impossible => by omega⟩⟩
    · intro r stable
      have neq : r ≠ 7 := fun eq => stable (eq.symm ▸ (by decide : (7 : ℕ) ∈ [7, 9, 11, 12, 13, 44, 45]))
      exact Function.update_of_ne neq _ _
    · intro v
      simp [first, SupportFromPrefix, zeros]
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 8 = I.graph.q :=
    ⟨hm.entry, hm.running, hm.index, hm.frame.count⟩
  have iterate (i : ℕ) (bound : i < I.graph.q) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns primSupportCell 12 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)} := by
    let e : Fin I.graph.q := ⟨i, bound⟩
    obtain ⟨t, run, ready, fixed, cursorAt, tail, rm, rr, nm⟩ :=
      primSupportCell_correct hm.frame hm.entry hm.running e hm.cursor
    let next := {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)}
    have stable (r : ℕ) (unchanged : r ∉ ([7, 9, 11, 12, 13, 44, 45] : List ℕ)) : next.nr r = m.nr r := by
      have neq : r ≠ 7 := fun eq => unchanged (eq.symm ▸ (by decide : (7 : ℕ) ∈ [7, 9, 11, 12, 13, 44, 45]))
      change Function.update t.nr 7 (t.nr 7 + t.nr 6) r = m.nr r
      rw [Function.update_of_ne neq]
      exact fixed r (fun included => unchanged (List.mem_cons_of_mem _ included))
    have preserves (k : ℕ) (outside : ¬(support ≤ k ∧ k < support + I.graph.n)) :
        next.nm k = m.nm k := by
      change t.nm k = _
      rw [nm]
      exact assignRequiredSupport_outside support e m.nm k outside
    have below (k : ℕ) (below : k < support) : next.nm k = m.nm k :=
      preserves k (fun h => (not_le.mpr below) h.1)
    have newFrame : PrimSupportFrame I rows matrix support next :=
      ⟨⟨(stable 3 (by decide)).trans hm.frame.floyd.tableBase,
        (stable 4 (by decide)).trans hm.frame.floyd.matrixBase,
        (stable 5 (by decide)).trans hm.frame.floyd.dimension,
        (stable 6 (by decide)).trans hm.frame.floyd.one,
        fun j hj => (below _ ((Nat.add_lt_add_left hj _).trans_le hm.frame.rowsBelow)).trans
          (hm.frame.floyd.rows j hj)⟩, (stable 8 (by decide)).trans hm.frame.count,
        (stable 40 (by decide)).trans hm.frame.base, (stable 33 (by decide)).trans hm.frame.zero,
        fun j hj => (below _ (hj.trans_le hm.frame.inputBelow)).trans (hm.frame.input j hj),
        hm.frame.inputBelow, hm.frame.rowsBelow⟩
    refine ⟨t, run, ready, rfl, ready, ?_, ?_, newFrame,
      fun r h => (stable r h).trans (hm.fixed r h), rm.trans hm.rm, rr.trans hm.rr,
      fun k h => (preserves k h).trans (hm.outside k h), ?_, ?_⟩
    · simp [next, fixed 7 (by decide), fixed 6 (by decide), hm.index, hm.frame.floyd.one]
    · simpa [next] using cursorAt
    · intro v
      change t.nm _ = _
      rw [nm, assignRequiredSupport_at, hm.bits]
      have grows : SupportFromPrefix I (i + 1) v ↔ SupportFromPrefix I i v ∨
          (e ∈ I.links ∧ (I.graph.tail e = v ∨ I.graph.head e = v)) := supportFromPrefix_next i bound v
      simp only [grows]
      by_cases present : e ∈ I.links ∧ (I.graph.tail e = v ∨ I.graph.head e = v)
      · rw [if_pos present, if_pos (Or.inr present)]
      · rw [if_neg present]
        simp only [present, or_false]
    · have now : next.nr 45 = rememberRequiredTail I e (m.nr 45) := by simpa [next] using tail
      by_cases needed : e ∈ I.links
      · refine Or.inr ⟨e, Nat.lt_succ_self _, needed, ?_⟩
        change next.nr 45 = (I.graph.tail e).val
        simpa [rememberRequiredTail, needed] using now
      · have same : next.nr 45 = m.nr 45 := by simpa [rememberRequiredTail, needed] using now
        rcases hm.root with ⟨none, absent⟩ | ⟨f, earlier, required, rootAt⟩
        · refine Or.inl ⟨same.trans none, fun f later required => ?_⟩
          by_cases eq : f.val = i
          · have same : f = e := Fin.ext eq
            exact needed (same ▸ required)
          · exact absent f (by omega) required
        · exact Or.inr ⟨f, earlier.trans (Nat.lt_succ_self _), required, same.trans rootAt⟩
  obtain ⟨last, complete, run⟩ :=
    countedLoopFromZero_correct 6 7 8 I.graph.q 12 primSupportCell inv entry running initial control iterate
  obtain ⟨edge, needed⟩ := nonempty
  rcases complete.root with ⟨_, absent⟩ | ⟨link, _, mark, rootAt⟩
  · exact False.elim (absent edge edge.isLt needed)
  · let finish := relocateState 1 {last with pc := (countedLoop 6 7 8 primSupportCell).length}
    let f := complete.frame
    have finalFrame : PrimSupportFrame I rows matrix support finish :=
      ⟨⟨f.floyd.tableBase, f.floyd.matrixBase, f.floyd.dimension, f.floyd.one, f.floyd.rows⟩,
        f.count, f.base, f.zero, f.input, f.inputBelow, f.rowsBelow⟩
    have ticks : 1 + (I.graph.q * (12 + 3) + 1) = 15 * I.graph.q + 2 := by omega
    refine ⟨finish, I.graph.tail link, by simpa only [primSupportScanBlock, ticks] using run,
      complete.running, finalFrame, complete.fixed, rootAt,
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ mark),
      complete.rm, complete.rr, complete.outside, ?_⟩
    intro v
    change last.nm _ = _
    rw [complete.bits]
    simp only [supportFromPrefix_all]

end VehicleRoutingSurvey.Routing
end RppSource_PrimSupport

/-! runtime/PrimLogic.lean -/
section RppSource_PrimLogic
namespace VehicleRoutingSurvey.Routing

abbrev PrimPair (I : Service) := Fin I.graph.n × Fin I.graph.n

def PrimCutEligible (I : Service) (visited : Finset (RequiredComponent I)) (p : PrimPair I) : Prop :=
  p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I ∧
    requiredComponent I p.1 ∈ visited ∧ requiredComponent I p.2 ∉ visited

abbrev PrimStep (I : Service) (chosen : List (PrimPair I)) (u v : Fin I.graph.n) : Prop :=
  requiredAdjacent I u v ∨ (u, v) ∈ chosen ∨ (v, u) ∈ chosen

structure PrimPrefix (I : Service) (root : Fin I.graph.n)
    (visited : Finset (RequiredComponent I)) (chosen : List (PrimPair I)) : Prop where
  requiredRoot : root ∈ requiredVertices I
  containsRoot : requiredComponent I root ∈ visited
  activeOnly : visited ⊆ activeRequiredComponents I
  count : chosen.length + 1 = visited.card
  unique : chosen.Nodup
  valid : ∀ p ∈ chosen, p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I ∧
    ¬sameComponent I p.1 p.2
  internal : ∀ p ∈ chosen, requiredComponent I p.1 ∈ visited ∧ requiredComponent I p.2 ∈ visited
  reaches : ∀ u ∈ requiredVertices I, requiredComponent I u ∈ visited →
    Relation.ReflTransGen (PrimStep I chosen) root u
  optimum : ∃ tree, MinimumComponentTree I tree ∧ chosen ⊆ tree

private theorem primWalk_symm {I : Service} {chosen : List (PrimPair I)} {u v : Fin I.graph.n}
    (walk : Relation.ReflTransGen (PrimStep I chosen) u v) :
    Relation.ReflTransGen (PrimStep I chosen) v u := by
  let _ : Std.Symm (PrimStep I chosen) := ⟨fun _ _ step =>
    step.elim (fun required => Or.inl (requiredAdjacent_comm required))
      (fun added => Or.inr (added.elim Or.inr Or.inl))⟩
  exact @Std.Symm.symm _ _ Relation.ReflTransGen.stdSymm u v walk

theorem primPrefix_initial {I : Service} (root : Fin I.graph.n)
    (needed : root ∈ requiredVertices I) :
    PrimPrefix I root {requiredComponent I root} [] := by
  classical
  obtain ⟨tree, minimum⟩ := exists_minimumComponentTree ⟨root, needed⟩
  refine ⟨needed, Finset.mem_singleton_self _, ?_, by simp, by simp,
    fun _ present => by simp at present, fun _ present => by simp at present, ?_,
    ⟨tree, minimum, List.nil_subset _⟩⟩
  · intro c member
    rw [Finset.mem_singleton.mp member]
    exact Finset.mem_image_of_mem _ needed
  · intro u _ seen
    have same := requiredComponent_eq_iff.mp (Finset.mem_singleton.mp seen).symm
    exact Relation.ReflTransGen.mono (fun _ _ step => Or.inl step) _ _ same

open Classical in
/-- Add one component by a cheapest oriented crossing pair. -/
theorem PrimPrefix.extend {I : Service} {root : Fin I.graph.n}
    {visited : Finset (RequiredComponent I)} {chosen : List (PrimPair I)}
    (current : PrimPrefix I root visited chosen) (undirected : Undirected I.graph)
    (edge : PrimPair I) (eligible : PrimCutEligible I visited edge)
    (cheapest : ∀ p, PrimCutEligible I visited p →
      distance I.graph edge.1 edge.2 ≤ distance I.graph p.1 p.2) :
    PrimPrefix I root (insert (requiredComponent I edge.2) visited) (edge :: chosen) := by
  obtain ⟨left, right, inside, outside⟩ := eligible
  have outsidePair : edge ∉ chosen := fun member => outside (current.internal edge member).2
  have distinct : ¬sameComponent I edge.1 edge.2 :=
    fun same => outside (requiredComponent_eq_iff.mpr same ▸ inside)
  have bothWays (p : PrimPair I) (uNeeded : p.1 ∈ requiredVertices I)
      (vNeeded : p.2 ∈ requiredVertices I) (crosses : CrossesRequiredCut (↑visited) p) :
      distance I.graph edge.1 edge.2 ≤ distance I.graph p.1 p.2 := by
    rcases crosses with forward | reverse
    · exact cheapest p ⟨uNeeded, vNeeded, forward⟩
    · exact (cheapest (p.2, p.1) ⟨vNeeded, uNeeded, reverse⟩).trans_eq
        (distance_symm undirected p.2 p.1)
  obtain ⟨oldTree, minimum, includes⟩ := current.optimum
  obtain ⟨tree, best, selected⟩ := extend_minimumComponentTree_across_cut (↑visited) edge left right
    inside outside bothWays minimum (chosen := chosen) (fun p member => by
      have ends := current.internal p member
      exact ⟨includes member, fun crossing => crossing.elim (fun h => h.2 ends.2) (fun h => h.2 ends.1)⟩)
  have lift {u v : Fin I.graph.n} (old : Relation.ReflTransGen (PrimStep I chosen) u v) :
      Relation.ReflTransGen (PrimStep I (edge :: chosen)) u v :=
    Relation.ReflTransGen.mono (fun _ _ step => step.elim Or.inl
      (fun use => Or.inr (use.imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)))) _ _ old
  refine ⟨current.requiredRoot, Finset.mem_insert_of_mem current.containsRoot, ?_, ?_,
    List.nodup_cons.mpr ⟨outsidePair, current.unique⟩, ?_, ?_, ?_, ⟨tree, best, fun p => selected p⟩⟩
  · intro c seen
    rcases Finset.mem_insert.mp seen with rfl | prior
    · exact Finset.mem_image_of_mem _ right
    · exact current.activeOnly prior
  · rw [Finset.card_insert_of_notMem outside, List.length_cons, current.count]
  · intro p member
    rcases List.mem_cons.mp member with rfl | prior
    · exact ⟨left, right, distinct⟩
    · exact current.valid p prior
  · intro p member
    rcases List.mem_cons.mp member with rfl | prior
    · exact ⟨Finset.mem_insert_of_mem inside, Finset.mem_insert_self _ _⟩
    · exact ⟨Finset.mem_insert_of_mem (current.internal p prior).1,
        Finset.mem_insert_of_mem (current.internal p prior).2⟩
  · intro u needed seen
    rcases Finset.mem_insert.mp seen with latest | prior
    · have reachesLeft := lift (current.reaches edge.1 left inside)
      have across : PrimStep I (edge :: chosen) edge.1 edge.2 := Or.inr (Or.inl List.mem_cons_self)
      have reachesWithin := Relation.ReflTransGen.mono
        (fun a b step => (Or.inl step : PrimStep I (edge :: chosen) a b)) _ _
        (requiredComponent_eq_iff.mp latest.symm)
      exact (reachesLeft.tail across).trans reachesWithin
    · exact lift (current.reaches u needed prior)

theorem PrimPrefix.exists_crossing {I : Service} {root : Fin I.graph.n}
    {visited : Finset (RequiredComponent I)} {chosen : List (PrimPair I)}
    (current : PrimPrefix I root visited chosen) (unfinished : visited ≠ activeRequiredComponents I) :
    ∃ p, PrimCutEligible I visited p := by
  classical
  by_contra absent
  apply unfinished
  apply Finset.Subset.antisymm current.activeOnly
  intro c active
  obtain ⟨v, required, rfl⟩ := Finset.mem_image.mp active
  by_contra outside
  exact absent ⟨(root, v), current.requiredRoot, required, current.containsRoot, outside⟩

theorem PrimPrefix.perm {I : Service} {root : Fin I.graph.n}
    {visited : Finset (RequiredComponent I)} {chosen reordered : List (PrimPair I)}
    (current : PrimPrefix I root visited chosen) (perm : chosen.Perm reordered) :
    PrimPrefix I root visited reordered := by
  refine ⟨current.requiredRoot, current.containsRoot, current.activeOnly,
    by rw [← perm.length_eq]; exact current.count, perm.nodup_iff.mp current.unique, ?_, ?_, ?_, ?_⟩
  · intro p inNew
    exact current.valid p (perm.mem_iff.mpr inNew)
  · intro p inNew
    exact current.internal p (perm.mem_iff.mpr inNew)
  · intro u needed seen
    exact Relation.ReflTransGen.mono (fun _ _ h => h.elim Or.inl
      (fun edges => Or.inr (edges.imp perm.mem_iff.mp perm.mem_iff.mp)))
      _ _ (current.reaches u needed seen)
  · obtain ⟨tree, minimum, contains⟩ := current.optimum
    exact ⟨tree, minimum, fun _ present => contains (perm.mem_iff.mpr present)⟩

open Classical in
theorem PrimPrefix.append {I : Service} {root : Fin I.graph.n}
    {visited : Finset (RequiredComponent I)} {chosen : List (PrimPair I)}
    (current : PrimPrefix I root visited chosen) (undirected : Undirected I.graph)
    (edge : PrimPair I) (eligible : PrimCutEligible I visited edge)
    (cheapest : ∀ p, PrimCutEligible I visited p →
      distance I.graph edge.1 edge.2 ≤ distance I.graph p.1 p.2) :
    PrimPrefix I root (insert (requiredComponent I edge.2) visited) (chosen ++ [edge]) :=
  (current.extend undirected edge eligible cheapest).perm
    (show ([edge] ++ chosen).Perm (chosen ++ [edge]) from List.perm_append_comm)

theorem requiredComponentCount_le_vertices (I : Service) :
    (activeRequiredComponents I).card ≤ I.graph.n := by
  classical
  have count := Finset.card_le_univ (requiredVertices I)
  unfold activeRequiredComponents
  exact Finset.card_image_le.trans (by simpa using count)

/-- A finished sequence of Prim choices is itself a minimum component tree. -/
theorem PrimPrefix.finish {I : Service} {root : Fin I.graph.n}
    {visited : Finset (RequiredComponent I)} {chosen : List (PrimPair I)}
    (current : PrimPrefix I root visited chosen) (finished : visited = activeRequiredComponents I) :
    MinimumComponentTree I chosen := by
  classical
  have seen (u : Fin I.graph.n) (needed : u ∈ requiredVertices I) :
      requiredComponent I u ∈ visited := by
    rw [finished]
    exact Finset.mem_image_of_mem _ needed
  have chosenCount : chosen.length + 1 = (activeRequiredComponents I).card :=
    current.count.trans (congrArg Finset.card finished)
  have tree : ComponentTree I chosen :=
    ⟨⟨requiredRepresentatives I, requiredRepresentatives_valid I,
      chosenCount.trans (requiredRepresentatives_length I).symm⟩, current.valid,
      fun u hu v hv => (primWalk_symm (current.reaches u hu (seen u hu))).trans
        (current.reaches v hv (seen v hv))⟩
  obtain ⟨minimum, best, inside⟩ := current.optimum
  obtain ⟨cs, reps, minCount⟩ := best.1.1
  have length : chosen.length = minimum.length :=
    Nat.add_right_cancel (chosenCount.trans (minCount.trans (componentRepresentatives_length reps)).symm)
  obtain ⟨p, rearranged, subset⟩ := List.subperm_iff.mp (current.unique.subperm inside)
  have whole : chosen = p := subset.eq_of_length (length.trans rearranged.length_eq.symm)
  have sameCost : pairCost I.graph chosen = pairCost I.graph minimum := by
    rw [whole]
    exact (rearranged.map (fun q => distance I.graph q.1 q.2)).sum_eq
  exact ⟨tree, fun qs good => sameCost.symm ▸ best.2 qs good⟩

end VehicleRoutingSurvey.Routing
end RppSource_PrimLogic

/-! runtime/MinimumKey.lean -/
section RppSource_MinimumKey
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Keep the earlier candidate on equal keys. A zero flag excludes a candidate. -/
noncomputable def preferMinimum (seen : ℕ × ℝ) (index flag : ℕ) (key : ℝ) : ℕ × ℝ :=
  if flag = 0 then seen else if seen.2 ≤ key then seen else (index, key)

/-- Compare one active key with the current minimum. Natural registers 1, 7,
and 8 supply the candidate index and the two array bases. Register 12 and
real register 0 hold the current minimizing index and key. -/
def minimumKeyCell : List ArithmeticInstruction :=
  [.natAdd 0 7 1, .natLoad 2 0, .natAdd 0 8 1, .realLoad 1 0,
    .natBranch 2 10 5 8, .jump 6, .jump 7, .jump 13,
    .realBranch 0 1 9 11, .jump 10, .jump 13, .realAdd 0 1 2, .natAdd 12 1 10]

theorem minimumKeyCell_correct {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (natZero : s.nr 10 = 0) (realZero : s.rr 2 = 0) :
    ∃ t, BlockRuns minimumKeyCell 8 s t ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      (∀ r, r ≠ 0 → r ≠ 2 → r ≠ 12 → t.nr r = s.nr r) ∧ (t.rr 2 = 0) ∧
      (t.nr 12, t.rr 0) = preferMinimum (s.nr 12, s.rr 0) (s.nr 1)
        (s.nm (s.nr 7 + s.nr 1)) (s.rm (s.nr 8 + s.nr 1)) := by
  let flag := s.nm (s.nr 7 + s.nr 1)
  let key := s.rm (s.nr 8 + s.nr 1)
  let loaded := {s with
    pc := 4
    nr := Function.update (Function.update s.nr 2 flag) 0 (s.nr 8 + s.nr 1)
    rr := Function.update s.rr 1 key}
  have read : (arithmeticStep minimumKeyCell)^[4] s = loaded := by
    simp [minimumKeyCell, arithmeticStep, entry, running, Function.iterate_succ_apply',
      loaded, flag, key, Function.update_comm (show (0 : ℕ) ≠ 2 by decide), Function.update_idem]
  have inside : ∀ j < 8, ((arithmeticStep minimumKeyCell)^[j] s).pc < minimumKeyCell.length := by
    intro j bound
    by_cases earlier : j < 4
    · have oneOf : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases oneOf with rfl | rfl | rfl | rfl <;>
        simp [minimumKeyCell, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt earlier)
      rw [Nat.add_comm 4 k, Function.iterate_add_apply, read]
      have oneOf : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      by_cases unavailable : flag = 0
      · rcases oneOf with rfl | rfl | rfl | rfl <;>
          simp [minimumKeyCell, arithmeticStep, loaded, running, natZero, unavailable,
            Function.iterate_succ_apply']
      · by_cases keep : s.rr 0 ≤ key <;>
          rcases oneOf with rfl | rfl | rfl | rfl <;>
          simp [minimumKeyCell, arithmeticStep, loaded, running, natZero, unavailable, keep,
            Function.iterate_succ_apply']
  by_cases unavailable : flag = 0
  · let t := {loaded with pc := 13}
    have result : (arithmeticStep minimumKeyCell)^[8] s = t := by
      rw [show (8 : ℕ) = 4 + 4 by decide, Function.iterate_add_apply, read]
      simp [minimumKeyCell, arithmeticStep, t, loaded, running, natZero,
        Function.iterate_succ_apply', unavailable]
    refine ⟨t, ⟨inside, result, rfl⟩, running, rfl, rfl, ?_, realZero, ?_⟩
    · intro r diff0 diff2 _
      simp [t, loaded, Function.update_of_ne diff0, Function.update_of_ne diff2]
    · simp [t, loaded, preferMinimum, flag, key, unavailable]
  by_cases keep : s.rr 0 ≤ key
  · let t := {loaded with pc := 13}
    have result : (arithmeticStep minimumKeyCell)^[8] s = t := by
      rw [show (8 : ℕ) = 4 + 4 by decide, Function.iterate_add_apply, read]
      simp [minimumKeyCell, arithmeticStep, t, loaded, running, natZero,
        Function.iterate_succ_apply', unavailable, keep]
    refine ⟨t, ⟨inside, result, rfl⟩, running, rfl, rfl, ?_, realZero, ?_⟩
    · intro r diff0 diff2 _
      simp [t, loaded, Function.update_of_ne diff0, Function.update_of_ne diff2]
    · simp [t, loaded, preferMinimum, flag, key, unavailable, keep]
  · let t := {loaded with
      pc := 13
      nr := Function.update loaded.nr 12 (s.nr 1)
      rr := Function.update loaded.rr 0 key}
    have result : (arithmeticStep minimumKeyCell)^[8] s = t := by
      rw [show (8 : ℕ) = 4 + 4 by decide, Function.iterate_add_apply, read]
      simp [minimumKeyCell, arithmeticStep, t, loaded, running, natZero, realZero,
        Function.iterate_succ_apply', unavailable, keep]
    refine ⟨t, ⟨inside, result, rfl⟩, running, rfl, rfl, ?_, realZero, ?_⟩
    · intro r diff0 diff2 diff12
      simp [t, loaded, Function.update_of_ne diff0, Function.update_of_ne diff2, Function.update_of_ne diff12]
    · simp [t, loaded, preferMinimum, flag, key, unavailable, keep]

noncomputable def minimumKeyPrefix (s : ArithmeticState) : ℕ → ℕ × ℝ
  | 0 => (s.nr 12, s.rr 0)
  | i + 1 => preferMinimum (minimumKeyPrefix s i) i
      (s.nm (s.nr 7 + i)) (s.rm (s.nr 8 + i))

theorem minimumKeyPrefix_spec (s : ArithmeticState) (i : ℕ) :
    ((minimumKeyPrefix s i).2 ≤ s.rr 0) ∧
      (∀ j < i, s.nm (s.nr 7 + j) ≠ 0 →
        (minimumKeyPrefix s i).2 ≤ s.rm (s.nr 8 + j)) ∧
      (minimumKeyPrefix s i = (s.nr 12, s.rr 0) ∨
        ∃ j < i, s.nm (s.nr 7 + j) ≠ 0 ∧
          minimumKeyPrefix s i = (j, s.rm (s.nr 8 + j))) := by
  induction i with
  | zero => simp [minimumKeyPrefix]
  | succ i ih =>
    let prior := minimumKeyPrefix s i
    let flag := s.nm (s.nr 7 + i)
    let key := s.rm (s.nr 8 + i)
    have keep (same : minimumKeyPrefix s (i + 1) = prior)
        (current : flag ≠ 0 → prior.2 ≤ key) :
        ((minimumKeyPrefix s (i + 1)).2 ≤ s.rr 0) ∧
          (∀ j < i + 1, s.nm (s.nr 7 + j) ≠ 0 →
            (minimumKeyPrefix s (i + 1)).2 ≤ s.rm (s.nr 8 + j)) ∧
          (minimumKeyPrefix s (i + 1) = (s.nr 12, s.rr 0) ∨
            ∃ j < i + 1, s.nm (s.nr 7 + j) ≠ 0 ∧
              minimumKeyPrefix s (i + 1) = (j, s.rm (s.nr 8 + j))) := by
      rw [same]
      refine ⟨ih.1, ?_, ?_⟩
      · intro j bound active
        by_cases equal : j = i
        · subst j
          exact current active
        · exact ih.2.1 j (by omega) active
      · rcases ih.2.2 with original | ⟨j, bound, active, selected⟩
        · exact Or.inl original
        · exact Or.inr ⟨j, by omega, active, selected⟩
    by_cases disabled : flag = 0
    · exact keep (by change preferMinimum prior i flag key = prior; simp [preferMinimum, disabled])
        (fun active => (active disabled).elim)
    by_cases noImprovement : prior.2 ≤ key
    · exact keep (by
        change preferMinimum prior i flag key = prior
        simp [preferMinimum, disabled, noImprovement]) (fun _ => noImprovement)
    have selected : minimumKeyPrefix s (i + 1) = (i, key) := by
      change preferMinimum prior i flag key = (i, key)
      simp [preferMinimum, disabled, noImprovement]
    rw [selected]
    have improves : key ≤ prior.2 := (lt_of_not_ge noImprovement).le
    refine ⟨improves.trans ih.1, ?_, Or.inr ⟨i, Nat.lt_succ_self i, disabled, rfl⟩⟩
    intro j bound active
    by_cases equal : j = i
    · subst j
      exact le_rfl
    · exact improves.trans (ih.2.1 j (by omega) active)

def minimumKeyScan : List ArithmeticInstruction :=
  countedLoopFromZero 6 1 5 minimumKeyCell

private structure MinimumKeyScanInvariant (start : ArithmeticState) (i : ℕ)
    (current : ArithmeticState) : Prop where
  entry : current.pc = 0
  running : current.halted = false
  index : current.nr 1 = i
  stable : ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 12 → current.nr r = start.nr r
  natMemory : current.nm = start.nm
  realMemory : current.rm = start.rm
  realZero : current.rr 2 = 0
  picked : (current.nr 12, current.rr 0) = minimumKeyPrefix start i

/-- Scan the key array, preserving both arrays and all unrelated natural
registers. The initial minimizing index and key serve as the default. -/
theorem minimumKeyScan_correct {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 6 = 1)
    (natZero : s.nr 10 = 0) (realZero : s.rr 2 = 0) :
    ∃ t, BlockRuns minimumKeyScan (1 + (s.nr 5 * 11 + 1)) s t ∧
      t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr 2 = 0 ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 12 → t.nr r = s.nr r) ∧
      (t.nr 12, t.rr 0) = minimumKeyPrefix s (s.nr 5) := by
  have initial : MinimumKeyScanInvariant s 0
      {s with pc := 0, nr := Function.update s.nr 1 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, rfl, realZero, ?_⟩
    · intro r _ diff1 _ _
      exact Function.update_of_ne diff1 _ _
    · simp [minimumKeyPrefix]
  have control (i : ℕ) (m : ArithmeticState) (inv : MinimumKeyScanInvariant s i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 1 = i ∧ m.nr 5 = s.nr 5 :=
    ⟨inv.entry, inv.running, inv.index, inv.stable 5 (by decide) (by decide)
      (by decide) (by decide)⟩
  have iterate (i : ℕ) (_ : i < s.nr 5) (m : ArithmeticState)
      (inv : MinimumKeyScanInvariant s i m) : ∃ t,
      BlockRuns minimumKeyCell 8 m t ∧ t.halted = false ∧
        MinimumKeyScanInvariant s (i + 1)
          {t with pc := 0, nr := Function.update t.nr 1 (t.nr 1 + t.nr 6)} := by
    have stableSix : m.nr 6 = 1 :=
      (inv.stable 6 (by decide) (by decide) (by decide) (by decide)).trans one
    have stableTen : m.nr 10 = 0 :=
      (inv.stable 10 (by decide) (by decide) (by decide) (by decide)).trans natZero
    have stableSeven := inv.stable 7 (by decide) (by decide) (by decide) (by decide)
    have stableEight := inv.stable 8 (by decide) (by decide) (by decide) (by decide)
    obtain ⟨t, runs, ready, nm, rm, stable, rr, choice⟩ :=
      minimumKeyCell_correct inv.entry inv.running stableTen inv.realZero
    have index := (stable 1 (by decide) (by decide) (by decide)).trans inv.index
    have increment := (stable 6 (by decide) (by decide) (by decide)).trans stableSix
    refine ⟨t, runs, ready, ⟨rfl, ready, ?_, ?_, nm.trans inv.natMemory,
      rm.trans inv.realMemory, rr, ?_⟩⟩
    · simp [index, increment]
    · intro r diff0 diff1 diff2 diff12
      exact (Function.update_of_ne diff1 _ _).trans <|
        (stable r diff0 diff2 diff12).trans (inv.stable r diff0 diff1 diff2 diff12)
    · rw [inv.picked, inv.natMemory, inv.realMemory, stableSeven, stableEight,
        inv.index] at choice
      simpa [minimumKeyPrefix] using choice
  obtain ⟨last, inv, run⟩ := countedLoopFromZero_correct 6 1 5 (s.nr 5) 8
    minimumKeyCell (MinimumKeyScanInvariant s) entry running initial control iterate
  exact ⟨_, run, inv.running, inv.natMemory, inv.realMemory, inv.realZero,
    inv.stable, inv.picked⟩


end VehicleRoutingSurvey.Routing
end RppSource_MinimumKey

/-! runtime/PrimMinimumScan.lean -/
section RppSource_PrimMinimumScan
namespace VehicleRoutingSurvey.Routing

def primPairOffset {n : ℕ} (p : Fin n × Fin n) : ℕ :=
  n * p.1.val + p.2.val

theorem primPairOffset_lt {n : ℕ} (p : Fin n × Fin n) : primPairOffset p < n ^ 2 := by
  rw [primPairOffset, pow_two]
  calc
    _ < n * (p.1.val + 1) := by
      rw [Nat.mul_succ]
      exact Nat.add_lt_add_left p.2.isLt _
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt p.1.isLt)

def primPairAtOffset {n : ℕ} (positive : 0 < n) (i : Fin (n ^ 2)) : Fin n × Fin n :=
  (⟨i.val / n, (Nat.div_lt_iff_lt_mul positive).mpr (by simpa only [pow_two] using i.isLt)⟩,
    ⟨i.val % n, Nat.mod_lt _ positive⟩)

theorem primPairAtOffset_index {n : ℕ} (positive : 0 < n) (i : Fin (n ^ 2)) :
    primPairOffset (primPairAtOffset positive i) = i.val :=
  Nat.div_add_mod _ _

theorem primPairOffset_injective {n : ℕ} :
    Function.Injective (@primPairOffset n) := by
  intro p q same
  obtain ⟨row, column⟩ := (denseMatrixOffset_eq_iff p.2.isLt q.2.isLt).mp same
  exact Prod.ext (Fin.ext row) (Fin.ext column)

/-- A dense mask of oriented crossing pairs lets the existing minimum-key
machine identify either a cheapest pair or a completed cut in one scan. -/
theorem primMinimumMaskScan_correct {I : Service} {root : Fin I.graph.n}
    {visited : Finset (RequiredComponent I)} {chosen : List (PrimPair I)}
    (current : PrimPrefix I root visited chosen) {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (zero : s.nr 10 = 0) (realZero : s.rr 2 = 0)
    (count : s.nr 5 = I.graph.n ^ 2) (noneYet : s.nr 12 = s.nr 5)
    (masks : ∀ p : PrimPair I, s.nm (s.nr 7 + primPairOffset p) ≠ 0 ↔ PrimCutEligible I visited p)
    (weights : ∀ p : PrimPair I, s.rm (s.nr 8 + primPairOffset p) = distance I.graph p.1 p.2)
    (sentinel : ∀ p : PrimPair I, distance I.graph p.1 p.2 < s.rr 0) :
    ∃ t, BlockRuns minimumKeyScan (11 * I.graph.n ^ 2 + 2) s t ∧ t.halted = false ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 12 → t.nr r = s.nr r) ∧
      ((t.nr 12 = s.nr 5 ∧ visited = activeRequiredComponents I) ∨
        ∃ p : PrimPair I, t.nr 12 = primPairOffset p ∧ t.rr 0 = distance I.graph p.1 p.2 ∧
          PrimCutEligible I visited p ∧ ∀ q : PrimPair I, PrimCutEligible I visited q →
            distance I.graph p.1 p.2 ≤ distance I.graph q.1 q.2) := by
  obtain ⟨t, executes, ready, nm, rm, _, fixed, chosenCell⟩ :=
    minimumKeyScan_correct entry running one zero realZero
  let best := minimumKeyPrefix s (s.nr 5)
  obtain ⟨_, belowCandidates, result⟩ := minimumKeyPrefix_spec s (s.nr 5)
  have less (p : PrimPair I) (eligible : PrimCutEligible I visited p) :
      best.2 ≤ distance I.graph p.1 p.2 := by
    have bounded : primPairOffset p < s.nr 5 := by rw [count]; exact primPairOffset_lt p
    have value := belowCandidates _ bounded ((masks p).mpr eligible)
    simpa [best, weights p] using value
  have steps : 1 + (s.nr 5 * 11 + 1) = 11 * I.graph.n ^ 2 + 2 := by
    rw [count]
    omega
  refine ⟨t, by simpa only [steps] using executes, ready, nm, rm, fixed, ?_⟩
  change best = (s.nr 12, s.rr 0) ∨ _ at result
  rcases result with unchanged | ⟨i, within, active, found⟩
  · left
    have named := congrArg Prod.fst (chosenCell.trans unchanged)
    refine ⟨named.trans noneYet, ?_⟩
    by_contra unfinished
    obtain ⟨p, crossing⟩ := current.exists_crossing unfinished
    have minimum := less p crossing
    rw [unchanged] at minimum
    exact (not_le.mpr (sentinel p)) minimum
  · right
    have positive : 0 < I.graph.n := (Nat.zero_le _).trans_lt root.isLt
    let index : Fin (I.graph.n ^ 2) := ⟨i, count ▸ within⟩
    let p := primPairAtOffset positive index
    have indexEq : primPairOffset p = i := primPairAtOffset_index positive index
    have label := congrArg Prod.fst (chosenCell.trans found)
    have key := congrArg Prod.snd (chosenCell.trans found)
    have readyPair : PrimCutEligible I visited p := (masks p).mp (indexEq.symm ▸ active)
    have keyAt : s.rm (s.nr 8 + i) = distance I.graph p.1 p.2 := by
      rw [← indexEq, weights p]
    refine ⟨p, label.trans indexEq.symm, key.trans keyAt, readyPair, fun q possible => ?_⟩
    have bestKey : best.2 = distance I.graph p.1 p.2 := (congrArg Prod.snd found).trans keyAt
    exact bestKey ▸ less q possible

end VehicleRoutingSurvey.Routing
end RppSource_PrimMinimumScan

/-! runtime/PrimMask.lean -/
section RppSource_PrimMask
namespace VehicleRoutingSurvey.Routing

def primMaskBit (fromVisited targetRequired targetVisited : Bool) : ℕ :=
  if fromVisited && targetRequired && !targetVisited then 1 else 0

private theorem primMaskBit_arithmetic (fromVisited targetRequired targetVisited : Bool) :
    ((if fromVisited then 1 else 0) + (if targetRequired then 1 else 0)) -
      (1 + (if targetVisited then 1 else 0)) = primMaskBit fromVisited targetRequired targetVisited := by
  cases fromVisited <;> cases targetRequired <;> cases targetVisited <;> decide

/-- Construct a crossing-pair mask cell from the two visited flags and the
target's required-support flag. Only arithmetic and indexed memory are used. -/
def primMaskCell : List ArithmeticInstruction :=
  [.natAdd 44 41 34, .natLoad 45 44, .natAdd 44 40 35, .natLoad 46 44,
    .natAdd 44 41 35, .natLoad 47 44, .natAdd 45 45 46, .natAdd 46 6 47, .natSub 45 45 46,
    .natAdd 44 3 34, .natLoad 44 44, .natAdd 44 44 35, .natAdd 44 42 44, .natStore 44 45]

private def primMaskCellState (s : ArithmeticState) : ArithmeticState :=
  let sourceFlag := s.nr 41 + s.nr 34
  let requiredFlag := s.nr 40 + s.nr 35
  let targetFlag := s.nr 41 + s.nr 35
  let sources := s.nm sourceFlag
  let needed := s.nm requiredFlag
  let targets := s.nm targetFlag
  let mask := (sources + needed) - (s.nr 6 + targets)
  let address := s.nr 42 + (s.nm (s.nr 3 + s.nr 34) + s.nr 35)
  let nr := Function.update (Function.update s.nr 44 sourceFlag) 45 sources
  let nr := Function.update (Function.update nr 44 requiredFlag) 46 needed
  let nr := Function.update (Function.update nr 44 targetFlag) 47 targets
  let nr := Function.update (Function.update nr 45 (sources + needed)) 46 (s.nr 6 + targets)
  let nr := Function.update (Function.update nr 45 mask) 44 address
  {s with pc := 14, nr := nr, nm := Function.update s.nm address mask}

private theorem primMaskCell_runs {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) : BlockRuns primMaskCell 14 s (primMaskCellState s) := by
  refine ⟨?_, ?_, rfl⟩
  · have position (i : ℕ) (hi : i ≤ 14) :
        ((arithmeticStep primMaskCell)^[i] s).pc = i ∧
          ((arithmeticStep primMaskCell)^[i] s).halted = false := by
      induction i with
      | zero => exact ⟨entry, running⟩
      | succ i ih =>
        have before : i < 14 := by omega
        have previous := ih before.le
        rw [Function.iterate_succ_apply']
        simp only [arithmeticStep, previous.1, previous.2, Bool.false_eq_true, ↓reduceIte]
        interval_cases i <;> exact ⟨rfl, rfl⟩
    intro i hi
    change ((arithmeticStep primMaskCell)^[i] s).pc < 14
    rwa [(position i (by omega)).1]
  · simp [primMaskCellState, primMaskCell, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Function.update_idem]

structure PrimMaskFrame (n rows matrix support visits mask : ℕ)
    (required seen : Fin n → Bool) (s : ArithmeticState) : Prop where
  floyd : FloydFrame n rows matrix s
  supportBase : s.nr 40 = support
  visitedBase : s.nr 41 = visits
  maskBase : s.nr 42 = mask
  supportBeforeMask : support + n ≤ mask
  visitsBeforeMask : visits + n ≤ mask
  rowsBeforeMask : rows + n ≤ mask
  supportBit : ∀ u : Fin n, s.nm (support + u.val) = if required u then 1 else 0
  visitedBit : ∀ u : Fin n, s.nm (visits + u.val) = if seen u then 1 else 0

theorem primMaskCell_correct {n rows matrix support visits mask : ℕ}
    {required seen : Fin n → Bool} {s : ArithmeticState}
    (frame : PrimMaskFrame n rows matrix support visits mask required seen s)
    (entry : s.pc = 0) (running : s.halted = false)
    (u v : Fin n) (row : s.nr 34 = u.val) (column : s.nr 35 = v.val) :
    ∃ t, BlockRuns primMaskCell 14 s t ∧ t.halted = false ∧
      (∀ r < 44, t.nr r = s.nr r) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      t.nm = Function.update s.nm (mask + primPairOffset (u, v))
        (primMaskBit (seen u) (required v) (seen v)) := by
  let t := primMaskCellState s
  refine ⟨t, primMaskCell_runs entry running, running, ?_, rfl, rfl, ?_⟩
  · intro r before
    simp [t, primMaskCellState, Function.update_of_ne (show r ≠ 44 by omega),
      Function.update_of_ne (show r ≠ 45 by omega), Function.update_of_ne (show r ≠ 46 by omega),
      Function.update_of_ne (show r ≠ 47 by omega)]
  · simp [t, primMaskCellState, frame.floyd.one, frame.floyd.tableBase, frame.floyd.rows _ u.isLt,
      frame.visitedBase, frame.supportBase, frame.maskBase, row, column, frame.supportBit,
      frame.visitedBit, primPairOffset, primMaskBit_arithmetic]

theorem primMaskBit_eligible {I : Service} {visited : Finset (RequiredComponent I)}
    (p : PrimPair I) (required seen : Fin I.graph.n → Bool)
    (requiredSpec : ∀ v, required v = true ↔ v ∈ requiredVertices I)
    (seenSpec : ∀ v, seen v = true ↔
      v ∈ requiredVertices I ∧ requiredComponent I v ∈ visited) :
    primMaskBit (seen p.1) (required p.2) (seen p.2) ≠ 0 ↔ PrimCutEligible I visited p := by
  have flag : primMaskBit (seen p.1) (required p.2) (seen p.2) ≠ 0 ↔
      seen p.1 = true ∧ required p.2 = true ∧ seen p.2 ≠ true := by
    generalize seen p.1 = a
    generalize required p.2 = b
    generalize seen p.2 = c
    cases a <;> cases b <;> cases c <;> decide
  rw [flag, seenSpec, requiredSpec]
  constructor
  · rintro ⟨⟨left, inside⟩, right, outside⟩
    exact ⟨left, right, inside, fun inCut => outside ((seenSpec p.2).mpr ⟨right, inCut⟩)⟩
  · rintro ⟨left, right, inside, outside⟩
    exact ⟨⟨left, inside⟩, right, fun marked => outside ((seenSpec p.2).mp marked).2⟩

end VehicleRoutingSurvey.Routing
end RppSource_PrimMask

/-! runtime/PrimMaskSweep.lean -/
section RppSource_PrimMaskSweep
namespace VehicleRoutingSurvey.Routing

private theorem PrimMaskFrame.copyStatic {n rows matrix support visits mask : ℕ}
    {required seen : Fin n → Bool} {s t : ArithmeticState}
    (frame : PrimMaskFrame n rows matrix support visits mask required seen s)
    (fixed : ∀ r < 44, r ≠ 34 → r ≠ 35 → t.nr r = s.nr r)
    (memory : ∀ k < mask, t.nm k = s.nm k) :
    PrimMaskFrame n rows matrix support visits mask required seen t :=
  ⟨⟨(fixed 3 (by decide) (by decide) (by decide)).trans frame.floyd.tableBase,
    (fixed 4 (by decide) (by decide) (by decide)).trans frame.floyd.matrixBase,
    (fixed 5 (by decide) (by decide) (by decide)).trans frame.floyd.dimension,
    (fixed 6 (by decide) (by decide) (by decide)).trans frame.floyd.one,
    fun i hi => (memory _ ((Nat.add_lt_add_left hi _).trans_le frame.rowsBeforeMask)).trans
      (frame.floyd.rows i hi)⟩,
    (fixed 40 (by decide) (by decide) (by decide)).trans frame.supportBase,
    (fixed 41 (by decide) (by decide) (by decide)).trans frame.visitedBase,
    (fixed 42 (by decide) (by decide) (by decide)).trans frame.maskBase,
    frame.supportBeforeMask, frame.visitsBeforeMask, frame.rowsBeforeMask,
    fun v => (memory _ ((Nat.add_lt_add_left v.isLt _).trans_le frame.supportBeforeMask)).trans
      (frame.supportBit v),
    fun v => (memory _ ((Nat.add_lt_add_left v.isLt _).trans_le frame.visitsBeforeMask)).trans
      (frame.visitedBit v)⟩

private def maskSweepMemory {n : ℕ} (step : Fin n → (ℕ → ℕ) → ℕ → ℕ)
    (count : ℕ) (memory : ℕ → ℕ) : ℕ → ℕ :=
  ((List.finRange n).take count).foldl (fun m i => step i m) memory

private theorem maskSweepMemory_succ {n : ℕ} (step : Fin n → (ℕ → ℕ) → ℕ → ℕ)
    (i : ℕ) (hi : i < n) (memory : ℕ → ℕ) :
    maskSweepMemory step (i + 1) memory = step ⟨i, hi⟩ (maskSweepMemory step i memory) := by
  have bound : i < (List.finRange n).length := by simpa using hi
  simp [maskSweepMemory, List.take_succ_eq_append_getElem bound, List.foldl_append]

private structure PrimMaskScanState (n rows matrix support visits mask control : ℕ)
    (required seen : Fin n → Bool) (step : Fin n → (ℕ → ℕ) → ℕ → ℕ)
    (keep : (ℕ → ℕ) → Prop) (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr control = i
  frame : PrimMaskFrame n rows matrix support visits mask required seen s
  stable : keep s.nr
  rm : s.rm = initial.rm
  rr : s.rr = initial.rr
  natural : s.nm = maskSweepMemory step i initial.nm

private theorem primMaskSweep_correct {n rows matrix support visits mask : ℕ}
    {required seen : Fin n → Bool} {s : ArithmeticState}
    (frame : PrimMaskFrame n rows matrix support visits mask required seen s)
    (entry : s.pc = 0) (running : s.halted = false)
    (control : ℕ) (isControl : control = 34 ∨ control = 35)
    (code : List ArithmeticInstruction) (ticks : ℕ)
    (step : Fin n → (ℕ → ℕ) → ℕ → ℕ) (keep : (ℕ → ℕ) → Prop)
    (initialKeep : keep (Function.update s.nr control 0))
    (advance : ∀ (i : Fin n) (m : ArithmeticState),
      PrimMaskFrame n rows matrix support visits mask required seen m →
      m.pc = 0 → m.halted = false → m.nr control = i.val → keep m.nr →
      ∃ t, BlockRuns code ticks m t ∧ t.halted = false ∧
        PrimMaskFrame n rows matrix support visits mask required seen t ∧ t.nr control = i.val ∧
        keep (Function.update t.nr control (i.val + 1)) ∧
        t.rm = m.rm ∧ t.rr = m.rr ∧ t.nm = step i m.nm) :
    ∃ t, BlockRuns (countedLoopFromZero 6 control 5 code) (1 + (n * (ticks + 3) + 1)) s t ∧
      t.halted = false ∧ PrimMaskFrame n rows matrix support visits mask required seen t ∧
      keep t.nr ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      t.nm = (List.finRange n).foldl (fun m i => step i m) s.nm := by
  let inv := PrimMaskScanState n rows matrix support visits mask control required seen step keep s
  let first := {s with pc := 0, nr := Function.update s.nr control 0}
  have firstFrame : PrimMaskFrame n rows matrix support visits mask required seen first := by
    refine frame.copyStatic (fun r _ noRow noCol => ?_) (fun _ _ => rfl)
    change Function.update s.nr control 0 r = s.nr r
    rw [Function.update_of_ne (by omega)]
  have initial : inv 0 first :=
    ⟨rfl, running, by simp [first], firstFrame, initialKeep, rfl, rfl, by simp [first, maskSweepMemory]⟩
  have controlAt (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr control = i ∧ m.nr 5 = n :=
    ⟨hm.entry, hm.running, hm.index, hm.frame.floyd.dimension⟩
  have iterate (i : ℕ) (hi : i < n) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns code ticks m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr control (t.nr control + t.nr 6)} := by
    let index : Fin n := ⟨i, hi⟩
    obtain ⟨t, run, ready, corner, position, stable, rm, rr, nm⟩ :=
      advance index m hm.frame hm.entry hm.running hm.index hm.stable
    let after := {t with pc := 0, nr := Function.update t.nr control (t.nr control + t.nr 6)}
    have afterFrame : PrimMaskFrame n rows matrix support visits mask required seen after := by
      refine corner.copyStatic (fun r _ noRow noCol => ?_) (fun _ _ => rfl)
      change Function.update t.nr control (t.nr control + t.nr 6) r = t.nr r
      rw [Function.update_of_ne (by omega)]
    refine ⟨t, run, ready, rfl, ready, ?_, afterFrame, ?_, rm.trans hm.rm, rr.trans hm.rr, ?_⟩
    · simp [position, corner.floyd.one, index]
    · simpa [position, corner.floyd.one, index] using stable
    · change t.nm = _
      rw [nm, hm.natural, maskSweepMemory_succ step i hi]
  obtain ⟨last, complete, run⟩ :=
    countedLoopFromZero_correct 6 control 5 n ticks code inv entry running initial controlAt iterate
  let finish := relocateState 1 {last with pc := (countedLoop 6 control 5 code).length}
  have lastFrame : PrimMaskFrame n rows matrix support visits mask required seen finish :=
    complete.frame.copyStatic (fun _ _ _ _ => rfl) (fun _ _ => rfl)
  have all : (List.finRange n).take n = List.finRange n := List.take_of_length_le (by simp)
  refine ⟨finish, run, complete.running, lastFrame, complete.stable, complete.rm, complete.rr, ?_⟩
  change last.nm = _
  simpa only [maskSweepMemory, all] using complete.natural

def primMaskRowBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 35 5 primMaskCell

def writePrimMask {n : ℕ} (mask : ℕ) (required seen : Fin n → Bool)
    (p : Fin n × Fin n) (memory : ℕ → ℕ) : ℕ → ℕ :=
  Function.update memory (mask + primPairOffset p)
    (primMaskBit (seen p.1) (required p.2) (seen p.2))

def primMaskRowMemory {n : ℕ} (mask : ℕ) (required seen : Fin n → Bool)
    (u : Fin n) (memory : ℕ → ℕ) : ℕ → ℕ :=
  (List.finRange n).foldl (fun m v => writePrimMask mask required seen (u, v) m) memory

abbrev PrimMaskRegisters (s t : ArithmeticState) : Prop :=
  ∀ r < 44, r ≠ 34 → r ≠ 35 → t.nr r = s.nr r

theorem primMaskRowBlock_correct {n rows matrix support visits mask : ℕ}
    {required seen : Fin n → Bool} {s : ArithmeticState}
    (frame : PrimMaskFrame n rows matrix support visits mask required seen s)
    (entry : s.pc = 0) (running : s.halted = false) (u : Fin n) (row : s.nr 34 = u.val) :
    ∃ t, BlockRuns primMaskRowBlock (17 * n + 2) s t ∧ t.halted = false ∧
      PrimMaskFrame n rows matrix support visits mask required seen t ∧ t.nr 34 = u.val ∧ PrimMaskRegisters s t ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ t.nm = primMaskRowMemory mask required seen u s.nm := by
  let keep (nr : ℕ → ℕ) : Prop := nr 34 = u.val ∧
    ∀ r < 44, r ≠ 34 → r ≠ 35 → nr r = s.nr r
  have initial : keep (Function.update s.nr 35 0) := by
    refine ⟨by simp [row], ?_⟩
    intro r _ _ different
    exact Function.update_of_ne different _ _
  obtain ⟨t, run, ready, finalFrame, rowStill, rm, rr, nm⟩ :=
    primMaskSweep_correct frame entry running 35 (.inr rfl) primMaskCell 14
      (fun v m => writePrimMask mask required seen (u, v) m) keep initial (by
        intro v m mFrame pc live column mRow
        obtain ⟨next, executes, ready, fixed, rm, rr, nm⟩ :=
          primMaskCell_correct mFrame pc live u v mRow.1 column
        have unchangedBelow (k : ℕ) (bound : k < mask) : next.nm k = m.nm k := by
          rw [nm, Function.update_of_ne (by omega)]
        have nextFrame := mFrame.copyStatic (fun r small _ _ => fixed r small) unchangedBelow
        refine ⟨next, executes, ready, nextFrame, (fixed 35 (by decide)).trans column, ?_, rm, rr, nm⟩
        refine ⟨by simp [fixed 34 (by decide), mRow.1], ?_⟩
        intro r small notRow notCol
        exact (Function.update_of_ne notCol _ _).trans
          ((fixed r small).trans (mRow.2 r small notRow notCol)))
  have ticks : 1 + (n * (14 + 3) + 1) = 17 * n + 2 := by omega
  exact ⟨t, by simpa only [primMaskRowBlock, ticks] using run,
    ready, finalFrame, rowStill.1, rowStill.2, rm, rr, nm⟩

def primMaskBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 34 5 primMaskRowBlock

def primMaskMemory {n : ℕ} (mask : ℕ) (required seen : Fin n → Bool) (memory : ℕ → ℕ) : ℕ → ℕ :=
  (List.finRange n).foldl (fun m u => primMaskRowMemory mask required seen u m) memory

theorem primMaskBlock_correct {n rows matrix support visits mask : ℕ}
    {required seen : Fin n → Bool} {s : ArithmeticState}
    (frame : PrimMaskFrame n rows matrix support visits mask required seen s)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns primMaskBlock (17 * n ^ 2 + 5 * n + 2) s t ∧ t.halted = false ∧
      PrimMaskFrame n rows matrix support visits mask required seen t ∧ PrimMaskRegisters s t ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ t.nm = primMaskMemory mask required seen s.nm := by
  let keep (nr : ℕ → ℕ) : Prop := ∀ r < 44, r ≠ 34 → r ≠ 35 → nr r = s.nr r
  have initial : keep (Function.update s.nr 34 0) := by
    intro r _ different _
    exact Function.update_of_ne different _ _
  obtain ⟨t, run, ready, finalFrame, stable, rm, rr, nm⟩ :=
    primMaskSweep_correct frame entry running 34 (.inl rfl) primMaskRowBlock (17 * n + 2)
      (fun u m => primMaskRowMemory mask required seen u m) keep initial (by
        intro u m mFrame pc live row prior
        obtain ⟨next, executes, ready, nextFrame, nextRow, fixed, rm, rr, nm⟩ :=
          primMaskRowBlock_correct mFrame pc live u row
        refine ⟨next, executes, ready, nextFrame, nextRow, ?_, rm, rr, nm⟩
        intro r small notRow notCol
        exact (Function.update_of_ne notRow _ _).trans
          ((fixed r small notRow notCol).trans (prior r small notRow notCol)))
  have ticks : 1 + (n * (17 * n + 2 + 3) + 1) = 17 * n ^ 2 + 5 * n + 2 := by ring
  exact ⟨t, by simpa only [primMaskBlock, ticks] using run, ready, finalFrame, stable, rm, rr, nm⟩

private theorem maskPairAddress_injective {n : ℕ} (mask : ℕ) :
    Function.Injective (fun p : Fin n × Fin n => mask + primPairOffset p) := by
  intro p q same
  obtain ⟨row, col⟩ := (denseMatrixOffset_eq_iff p.2.isLt q.2.isLt).mp (Nat.add_left_cancel same)
  exact Prod.ext (Fin.ext row) (Fin.ext col)

private theorem maskFold_at {n : ℕ} (mask : ℕ) (required seen : Fin n → Bool)
    (pairs : List (Fin n × Fin n)) (memory : ℕ → ℕ) (p : Fin n × Fin n) :
    (pairs.foldl (fun m q => writePrimMask mask required seen q m) memory) (mask + primPairOffset p) =
      if p ∈ pairs then primMaskBit (seen p.1) (required p.2) (seen p.2)
      else memory (mask + primPairOffset p) := by
  induction pairs generalizing memory with
  | nil => simp
  | cons q rest ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    by_cases later : p ∈ rest
    · simp [later]
    · by_cases matching : p = q
      · subst q
        simp [later, writePrimMask]
      · have differs : mask + primPairOffset p ≠ mask + primPairOffset q :=
          fun eq => matching (maskPairAddress_injective mask eq)
        simp [later, matching, writePrimMask, Function.update_of_ne differs]

theorem primMaskMemory_exact {n : ℕ} (mask : ℕ) (required seen : Fin n → Bool)
    (memory : ℕ → ℕ) (p : Fin n × Fin n) :
    primMaskMemory mask required seen memory (mask + primPairOffset p) =
      primMaskBit (seen p.1) (required p.2) (seen p.2) := by
  let pairs := (List.finRange n).flatMap (fun u => (List.finRange n).map (fun v => (u, v)))
  have present : p ∈ pairs := List.mem_flatMap.mpr ⟨p.1, List.mem_finRange p.1,
    List.mem_map.mpr ⟨p.2, List.mem_finRange p.2, Prod.eta p⟩⟩
  have exactCell := maskFold_at mask required seen pairs memory p
  rw [if_pos present] at exactCell
  simpa only [pairs, List.foldl_flatMap, List.foldl_map, primMaskMemory, primMaskRowMemory] using exactCell

theorem primMaskMemory_outside {n : ℕ} (mask : ℕ) (required seen : Fin n → Bool)
    (memory : ℕ → ℕ) (k : ℕ) (outside : ¬(mask ≤ k ∧ k < mask + n ^ 2)) :
    primMaskMemory mask required seen memory k = memory k := by
  have oneRow (u : Fin n) (m : ℕ → ℕ) : primMaskRowMemory mask required seen u m k = m k := by
    unfold primMaskRowMemory
    generalize List.finRange n = columns
    induction columns generalizing m with
    | nil => rfl
    | cons v rest ih =>
      rw [List.foldl_cons, ih]
      have distinct : k ≠ mask + primPairOffset (u, v) := by
        intro same
        apply outside
        rw [same]
        exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (primPairOffset_lt (u, v)) _⟩
      exact Function.update_of_ne distinct _ _
  unfold primMaskMemory
  generalize List.finRange n = rows
  induction rows generalizing memory with
  | nil => rfl
  | cons u rest ih => simp only [List.foldl_cons, ih, oneRow]

end VehicleRoutingSurvey.Routing
end RppSource_PrimMaskSweep

/-! runtime/PrimSelect.lean -/
section RppSource_PrimSelect
namespace VehicleRoutingSurvey.Routing

/-- Adapt the Floyd matrix and crossing mask to the existing flat
minimum-key scan. One read-only real cell immediately after the distance
matrix holds a sentinel larger than every distance. -/
private def preparePrimMinimum : List ArithmeticInstruction :=
  [.natConst 33 0, .natSub 44 5 6, .natAdd 44 3 44, .natLoad 44 44, .natAdd 44 44 5,
    .natAdd 50 5 33, .natAdd 5 44 33, .natAdd 7 42 33, .natAdd 8 4 33, .natConst 10 0,
    .natAdd 12 5 33, .realConst 2 0, .natAdd 51 4 44, .realLoad 0 51]

private def preparePrimMinimumState (s : ArithmeticState) : ArithmeticState :=
  let cells := s.nm (s.nr 3 + (s.nr 5 - s.nr 6)) + s.nr 5
  let upper := s.nr 4 + cells
  let nr := Function.update (Function.update s.nr 33 0) 44 cells
  let nr := Function.update (Function.update nr 50 (s.nr 5)) 5 cells
  let nr := Function.update (Function.update nr 7 (s.nr 42)) 8 (s.nr 4)
  let nr := Function.update (Function.update (Function.update nr 10 0) 12 cells) 51 upper
  {s with pc := 14, nr := nr, rr := Function.update (Function.update s.rr 2 0) 0 (s.rm upper)}

private def PrimPrepFixed (s t : ArithmeticState) : Prop :=
  ∀ r < 44, r ∉ ([5, 7, 8, 10, 12, 33] : List ℕ) → t.nr r = s.nr r

private structure PrimMinimumPrepared (n mask matrix : ℕ) (s t : ArithmeticState) : Prop where
  run : BlockRuns preparePrimMinimum 14 s t
  running : t.halted = false
  fixed : PrimPrepFixed s t
  nm : t.nm = s.nm
  rm : t.rm = s.rm
  count : t.nr 5 = n ^ 2
  maskBase : t.nr 7 = mask
  realBase : t.nr 8 = matrix
  one : t.nr 6 = 1
  zero : t.nr 10 = 0
  default : t.nr 12 = n ^ 2
  realZero : t.rr 2 = 0
  sentinel : t.rr 0 = s.rm (matrix + n ^ 2)
  savedDimension : t.nr 50 = n
  backupZero : t.nr 33 = 0
  flatLength : t.nr 44 = n ^ 2

private theorem preparePrimMinimum_correct {n rows matrix mask : ℕ} {s : ArithmeticState}
    (frame : FloydFrame n rows matrix s) (positive : 0 < n) (maskAt : s.nr 42 = mask)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, PrimMinimumPrepared n mask matrix s t := by
  let t := preparePrimMinimumState s
  have last : n - 1 < n := by omega
  have succLast : (n - 1).succ = n := by omega
  have cells : s.nm (s.nr 3 + (n - 1)) + n = n ^ 2 := by
    rw [frame.tableBase, frame.rows _ last, pow_two, ← Nat.mul_succ, succLast]
  have run : BlockRuns preparePrimMinimum 14 s t := by
    refine ⟨?_, ?_, rfl⟩
    · have counter (i : ℕ) (hi : i ≤ 14) :
          ((arithmeticStep preparePrimMinimum)^[i] s).pc = i ∧
            ((arithmeticStep preparePrimMinimum)^[i] s).halted = false := by
        induction i with
        | zero => exact ⟨entry, running⟩
        | succ i ih =>
          have below : i < 14 := by omega
          have before := ih below.le
          rw [Function.iterate_succ_apply']
          simp only [arithmeticStep, before.1, before.2, Bool.false_eq_true, ↓reduceIte]
          interval_cases i <;> exact ⟨rfl, rfl⟩
      intro i hi
      change ((arithmeticStep preparePrimMinimum)^[i] s).pc < 14
      rwa [(counter i (by omega)).1]
    · simp [t, preparePrimMinimumState, preparePrimMinimum, arithmeticStep, entry, running,
        Function.iterate_succ_apply', Function.update_idem]
  have fixed : PrimPrepFixed s t := by
    intro r low notWritten
    have different (i : ℕ) (used : i ∈ ([5, 7, 8, 10, 12, 33] : List ℕ)) : r ≠ i :=
      fun equal => notWritten (equal.symm ▸ used)
    simp [t, preparePrimMinimumState, Function.update_of_ne (different 5 (by decide)),
      Function.update_of_ne (different 7 (by decide)), Function.update_of_ne (different 8 (by decide)),
      Function.update_of_ne (different 10 (by decide)), Function.update_of_ne (different 12 (by decide)),
      Function.update_of_ne (different 33 (by decide)), Function.update_of_ne (show r ≠ 44 by omega),
      Function.update_of_ne (show r ≠ 50 by omega), Function.update_of_ne (show r ≠ 51 by omega)]
  refine ⟨t, run, running, fixed, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [t, preparePrimMinimumState, cells, frame.matrixBase, frame.dimension, frame.one, maskAt]

private def restorePrimDimension : List ArithmeticInstruction := [.natAdd 5 50 33]

def primSelectAcrossCutBlock : List ArithmeticInstruction :=
  appendBlock primMaskBlock
    (appendBlock preparePrimMinimum (appendBlock minimumKeyScan restorePrimDimension))

/-- Fill the crossing mask and select its cheapest pair. This block
restores the Floyd dimension and leaves the preceding memory intact. -/
theorem primSelectAcrossCutBlock_correct {I : Service} {root : Fin I.graph.n}
    {visited : Finset (RequiredComponent I)} {chosen : List (PrimPair I)}
    (current : PrimPrefix I root visited chosen)
    {rows matrix support visits mask : ℕ} {required seen : Fin I.graph.n → Bool} {s : ArithmeticState}
    (frame : PrimMaskFrame I.graph.n rows matrix support visits mask required seen s)
    (entry : s.pc = 0) (running : s.halted = false)
    (requiredSpec : ∀ v, required v = true ↔ v ∈ requiredVertices I)
    (seenSpec : ∀ v, seen v = true ↔ v ∈ requiredVertices I ∧ requiredComponent I v ∈ visited)
    (distances : ∀ p : PrimPair I, s.rm (matrix + primPairOffset p) = distance I.graph p.1 p.2)
    (sentinel : ∀ p : PrimPair I, distance I.graph p.1 p.2 < s.rm (matrix + I.graph.n ^ 2)) :
    ∃ t, BlockRuns primSelectAcrossCutBlock (28 * I.graph.n ^ 2 + 5 * I.graph.n + 19) s t ∧
      t.halted = false ∧ PrimMaskFrame I.graph.n rows matrix support visits mask required seen t ∧
      t.nr 33 = 0 ∧ t.nr 44 = I.graph.n ^ 2 ∧ t.rm = s.rm ∧
      (∀ r < 44, r ∉ ([0, 1, 2, 5, 7, 8, 10, 12, 33, 34, 35] : List ℕ) → t.nr r = s.nr r) ∧
      (∀ k, ¬(mask ≤ k ∧ k < mask + I.graph.n ^ 2) → t.nm k = s.nm k) ∧
      ((t.nr 12 = I.graph.n ^ 2 ∧ visited = activeRequiredComponents I) ∨
        ∃ p : PrimPair I, t.nr 12 = primPairOffset p ∧
          PrimCutEligible I visited p ∧ ∀ q : PrimPair I, PrimCutEligible I visited q →
            distance I.graph p.1 p.2 ≤ distance I.graph q.1 q.2) := by
  obtain ⟨masked, writes, maskedReady, maskFrame, maskFixed, maskRm, _, maskNm⟩ :=
    primMaskBlock_correct frame entry running
  let maskStart := {masked with pc := 0}
  have maskedFrame : FloydFrame I.graph.n rows matrix maskStart :=
    maskFrame.floyd.preserved (fun _ _ _ => rfl) rfl
  have positive : 0 < I.graph.n := (Nat.zero_le _).trans_lt root.isLt
  obtain ⟨prepared, prep⟩ :=
    preparePrimMinimum_correct (s := maskStart) maskedFrame positive maskFrame.maskBase rfl maskedReady
  let scanStart := {prepared with pc := 0}
  have masks (p : PrimPair I) :
      scanStart.nm (scanStart.nr 7 + primPairOffset p) ≠ 0 ↔ PrimCutEligible I visited p := by
    change prepared.nm (prepared.nr 7 + primPairOffset p) ≠ 0 ↔ _
    rw [prep.maskBase, prep.nm]
    change masked.nm _ ≠ 0 ↔ _
    rw [maskNm, primMaskMemory_exact]
    exact primMaskBit_eligible p required seen requiredSpec seenSpec
  have keys (p : PrimPair I) :
      scanStart.rm (scanStart.nr 8 + primPairOffset p) = distance I.graph p.1 p.2 := by
    change prepared.rm (prepared.nr 8 + primPairOffset p) = _
    rw [prep.realBase, prep.rm]
    change masked.rm _ = _
    rw [maskRm]
    exact distances p
  have high (p : PrimPair I) : distance I.graph p.1 p.2 < scanStart.rr 0 := by
    change _ < prepared.rr 0
    rw [prep.sentinel]
    change _ < masked.rm _
    rw [maskRm]
    exact sentinel p
  obtain ⟨selected, scanRun, scanReady, nm, rm, fixed, result⟩ :=
    primMinimumMaskScan_correct current (s := scanStart) rfl prep.running prep.one prep.zero
      prep.realZero prep.count (prep.default.trans prep.count.symm) masks keys high
  let reset := {selected with pc := 0}
  let restored := {selected with pc := 1, nr := Function.update selected.nr 5 I.graph.n}
  have saved : selected.nr 50 = I.graph.n :=
    (fixed 50 (by decide) (by decide) (by decide) (by decide)).trans prep.savedDimension
  have zero : selected.nr 33 = 0 :=
    (fixed 33 (by decide) (by decide) (by decide) (by decide)).trans prep.backupZero
  have flatLength : selected.nr 44 = I.graph.n ^ 2 :=
    (fixed 44 (by decide) (by decide) (by decide) (by decide)).trans prep.flatLength
  have restores : BlockRuns restorePrimDimension 1 reset restored := by
    refine ⟨?_, ?_, rfl⟩
    · intro i hi
      have only : i = 0 := by omega
      simp [only, reset, restorePrimDimension]
    · simp [restored, reset, restorePrimDimension, arithmeticStep, scanReady, saved, zero]
  let t := relocateState primMaskBlock.length (relocateState preparePrimMinimum.length
    (relocateState minimumKeyScan.length restored))
  have executes := writes.append (prep.run.append (scanRun.append restores))
  have finalMemory : t.nm = masked.nm := nm.trans prep.nm
  have stable (r : ℕ) (lower : r < 44) (avoids : r ∉ ([0, 1, 2, 5, 7, 8, 10, 12, 33] : List ℕ)) :
      t.nr r = masked.nr r := by
    have different (i : ℕ) (excluded : i ∈ ([0, 1, 2, 5, 7, 8, 10, 12, 33] : List ℕ)) :
        r ≠ i := fun equal => avoids (equal.symm ▸ excluded)
    have previous := fixed r (different 0 (by decide)) (different 1 (by decide))
      (different 2 (by decide)) (different 12 (by decide))
    have setUp := prep.fixed r lower (fun written => avoids (List.mem_append_right [0, 1, 2] written))
    change Function.update selected.nr 5 I.graph.n r = masked.nr r
    rw [Function.update_of_ne (different 5 (by decide))]
    exact previous.trans setUp
  have newFrame : PrimMaskFrame I.graph.n rows matrix support visits mask required seen t :=
    ⟨⟨(stable 3 (by decide) (by decide)).trans maskFrame.floyd.tableBase,
      (stable 4 (by decide) (by decide)).trans maskFrame.floyd.matrixBase, by simp [t, restored, relocateState],
      (stable 6 (by decide) (by decide)).trans maskFrame.floyd.one,
      fun i hi => (congrFun finalMemory _).trans (maskFrame.floyd.rows i hi)⟩,
      (stable 40 (by decide) (by decide)).trans maskFrame.supportBase,
      (stable 41 (by decide) (by decide)).trans maskFrame.visitedBase,
      (stable 42 (by decide) (by decide)).trans maskFrame.maskBase,
      maskFrame.supportBeforeMask, maskFrame.visitsBeforeMask, maskFrame.rowsBeforeMask,
      fun v => (congrFun finalMemory _).trans (maskFrame.supportBit v),
      fun v => (congrFun finalMemory _).trans (maskFrame.visitedBit v)⟩
  have steps : (17 * I.graph.n ^ 2 + 5 * I.graph.n + 2) + (14 + (11 * I.graph.n ^ 2 + 2 + 1)) =
      28 * I.graph.n ^ 2 + 5 * I.graph.n + 19 := by ring
  refine ⟨t, by simpa only [primSelectAcrossCutBlock, steps] using executes, scanReady,
    newFrame, by simpa [t, restored, relocateState] using zero,
    by simpa [t, restored, relocateState] using flatLength,
    (rm.trans prep.rm).trans maskRm, ?_, ?_, ?_⟩
  · intro r low avoids
    have different (i : ℕ) (excluded : i ∈ ([0, 1, 2, 5, 7, 8, 10, 12, 33, 34, 35] : List ℕ)) :
        r ≠ i := fun equal => avoids (equal.symm ▸ excluded)
    exact (stable r low (fun written => avoids (List.mem_append_left [34, 35] written))).trans
      (maskFixed r low (different 34 (by decide)) (different 35 (by decide)))
  · intro k outside
    rw [finalMemory, maskNm]
    exact primMaskMemory_outside mask required seen s.nm k outside
  · rcases result with ⟨missing, complete⟩ | ⟨p, found, _, valid, least⟩
    · exact Or.inl ⟨by simpa [t, restored, relocateState] using missing.trans prep.count, complete⟩
    · exact Or.inr ⟨p, by simpa [t, restored, relocateState] using found, valid, least⟩

end VehicleRoutingSurvey.Routing
end RppSource_PrimSelect

/-! runtime/PrimOffsetDecode.lean -/
section RppSource_PrimOffsetDecode
namespace VehicleRoutingSurvey.Routing

/-- Subtract one row length when possible. Both outcomes take three
instructions. Register 44 counts rows and register 45 is the remainder. -/
private def primOffsetDecodeCell : List ArithmeticInstruction :=
  [.natBranch 5 45 3 1, .jump 2, .jump 5, .natSub 45 45 5, .natAdd 44 44 6]

private theorem primOffsetDecodeCell_correct {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) :
    ∃ t, BlockRuns primOffsetDecodeCell 3 s t ∧ t.halted = false ∧
      (∀ r, r ≠ 44 → r ≠ 45 → t.nr r = s.nr r) ∧
      t.nr 44 = (if s.nr 5 ≤ s.nr 45 then s.nr 44 + s.nr 6 else s.nr 44) ∧
      t.nr 45 = (if s.nr 5 ≤ s.nr 45 then s.nr 45 - s.nr 5 else s.nr 45) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  by_cases step : s.nr 5 ≤ s.nr 45
  · let t := {s with
      pc := 5
      nr := Function.update (Function.update s.nr 45 (s.nr 45 - s.nr 5)) 44 (s.nr 44 + s.nr 6)}
    refine ⟨t, ⟨?_, ?_, rfl⟩, running, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · intro i hi
      interval_cases i <;>
        simp [primOffsetDecodeCell, arithmeticStep, entry, running, Function.iterate_succ_apply', step]
    · simp [t, primOffsetDecodeCell, arithmeticStep, entry, running, Function.iterate_succ_apply', step]
    · intro r first second
      simp [t, Function.update_of_ne first, Function.update_of_ne second]
    · simp [t, step]
    · simp [t, step]
  · let t := {s with pc := 5}
    refine ⟨t, ⟨?_, ?_, rfl⟩, running, fun _ _ _ => rfl, ?_, ?_, rfl, rfl, rfl⟩
    · intro i hi
      interval_cases i <;>
        simp [primOffsetDecodeCell, arithmeticStep, entry, running, Function.iterate_succ_apply', step]
    · simp [t, primOffsetDecodeCell, arithmeticStep, entry, running, Function.iterate_succ_apply', step]
    · simp [t, step]
    · simp [t, step]

private def primOffsetDecodeLoop : List ArithmeticInstruction :=
  countedLoopFromZero 6 7 5 primOffsetDecodeCell

private structure OffsetDecodeState (initial : ArithmeticState) (n offset i : ℕ)
    (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 7 = i
  count : s.nr 5 = n
  one : s.nr 6 = 1
  fixed : ∀ r, r ≠ 7 → r ≠ 44 → r ≠ 45 → s.nr r = initial.nr r
  encoded : n * s.nr 44 + s.nr 45 = offset
  unfinished : n ≤ s.nr 45 → s.nr 44 = i
  natural : s.nm = initial.nm
  realMemory : s.rm = initial.rm
  realRegisters : s.rr = initial.rr

private theorem primOffsetDecodeLoop_correct {n offset : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (count : s.nr 5 = n)
    (one : s.nr 6 = 1) (firstRow : s.nr 44 = 0) (initialOffset : s.nr 45 = offset)
    (within : offset < n ^ 2) :
    ∃ (t : ArithmeticState) (p : Fin n × Fin n), BlockRuns primOffsetDecodeLoop (6 * n + 2) s t ∧
      t.halted = false ∧ t.nr 44 = p.1.val ∧ t.nr 45 = p.2.val ∧ primPairOffset p = offset ∧
      (∀ r, r ≠ 7 → r ≠ 44 → r ≠ 45 → t.nr r = s.nr r) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  let inv := OffsetDecodeState s n offset
  let first := {s with pc := 0, nr := Function.update s.nr 7 0}
  have initial : inv 0 first := by
    refine ⟨rfl, running, by simp [first], count, one, ?_, ?_, fun _ => firstRow, rfl, rfl, rfl⟩
    · intro r stable _ _
      simp [first, Function.update_of_ne stable]
    · simp [first, firstRow, initialOffset]
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 5 = n :=
    ⟨hm.entry, hm.running, hm.index, hm.count⟩
  have iterate (i : ℕ) (_ : i < n) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns primOffsetDecodeCell 3 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)} := by
    obtain ⟨t, run, live, fixed, row, column, nm, rm, rr⟩ :=
      primOffsetDecodeCell_correct hm.entry hm.running
    refine ⟨t, run, live, rfl, live, ?_, ?_, ?_, ?_, ?_, ?_,
      nm.trans hm.natural, rm.trans hm.realMemory, rr.trans hm.realRegisters⟩
    · simp [fixed 7 (by decide) (by decide), fixed 6 (by decide) (by decide), hm.index, hm.one]
    · simpa using (fixed 5 (by decide) (by decide)).trans hm.count
    · simpa using (fixed 6 (by decide) (by decide)).trans hm.one
    · intro r notIndex rowReg colReg
      change Function.update t.nr 7 (t.nr 7 + t.nr 6) r = s.nr r
      rw [Function.update_of_ne notIndex, fixed r rowReg colReg, hm.fixed r notIndex rowReg colReg]
    · change n * t.nr 44 + t.nr 45 = offset
      rw [row, column, hm.count, hm.one]
      by_cases step : n ≤ m.nr 45
      · simp only [if_pos step, Nat.mul_succ]
        have total := hm.encoded
        omega
      · simpa only [if_neg step] using hm.encoded
    · change n ≤ t.nr 45 → t.nr 44 = i + 1
      rw [row, column, hm.count, hm.one]
      by_cases step : n ≤ m.nr 45
      · simp [step, hm.unfinished step]
      · simp only [if_neg step]
        exact fun condition => (step condition).elim
  obtain ⟨last, complete, run⟩ :=
    countedLoopFromZero_correct 6 7 5 n 3 primOffsetDecodeCell inv entry running initial control iterate
  have rowBound : last.nr 44 < n := by
    by_contra! tooFar
    have high := Nat.mul_le_mul_left n tooFar
    have total := complete.encoded
    rw [pow_two] at within
    omega
  have columnBound : last.nr 45 < n := by
    by_contra! large
    exact (Nat.ne_of_lt rowBound) (complete.unfinished large)
  let p : Fin n × Fin n := (⟨last.nr 44, rowBound⟩, ⟨last.nr 45, columnBound⟩)
  let finish := relocateState 1 {last with pc := (countedLoop 6 7 5 primOffsetDecodeCell).length}
  have ticks : 1 + (n * (3 + 3) + 1) = 6 * n + 2 := by omega
  exact ⟨finish, p, by simpa only [primOffsetDecodeLoop, ticks] using run,
    complete.running, rfl, rfl, complete.encoded,
    complete.fixed, complete.natural, complete.realMemory, complete.realRegisters⟩

private def seedPrimOffsetDecoder : List ArithmeticInstruction :=
  [.natConst 44 0, .natAdd 45 12 33]

def primOffsetDecodeBlock : List ArithmeticInstruction :=
  appendBlock seedPrimOffsetDecoder primOffsetDecodeLoop

/-- Decode the selected dense offset without a natural division opcode. -/
theorem primOffsetDecodeBlock_correct {n : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (count : s.nr 5 = n)
    (one : s.nr 6 = 1) (zero : s.nr 33 = 0) (within : s.nr 12 < n ^ 2) :
    ∃ (t : ArithmeticState) (p : Fin n × Fin n), BlockRuns primOffsetDecodeBlock (6 * n + 4) s t ∧
      t.halted = false ∧ t.nr 44 = p.1.val ∧ t.nr 45 = p.2.val ∧ primPairOffset p = s.nr 12 ∧
      (∀ r, r ≠ 7 → r ≠ 44 → r ≠ 45 → t.nr r = s.nr r) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  let seeded := {s with
    pc := 2
    nr := Function.update (Function.update s.nr 44 0) 45 (s.nr 12)}
  have seed : BlockRuns seedPrimOffsetDecoder 2 s seeded := by
    refine ⟨?_, ?_, rfl⟩
    · intro i bound
      interval_cases i <;> simp [seedPrimOffsetDecoder, arithmeticStep, entry, running]
    · simp [seeded, seedPrimOffsetDecoder, arithmeticStep, entry, running,
        Function.iterate_succ_apply', zero]
  let q := {seeded with pc := 0}
  have fixed (r : ℕ) (first : r ≠ 44) (second : r ≠ 45) : q.nr r = s.nr r := by
    simp [q, seeded, Function.update_of_ne first, Function.update_of_ne second]
  obtain ⟨t, p, run, ready, row, col, value, stable, nm, rm, rr⟩ :=
    primOffsetDecodeLoop_correct (s := q) (offset := s.nr 12) rfl running
      ((fixed 5 (by decide) (by decide)).trans count)
      ((fixed 6 (by decide) (by decide)).trans one)
      (by simp [q, seeded]) (by simp [q, seeded]) within
  let finish := relocateState seedPrimOffsetDecoder.length t
  have ticks : 2 + (6 * n + 2) = 6 * n + 4 := by omega
  refine ⟨finish, p, by simpa only [primOffsetDecodeBlock, ticks] using seed.append run,
    ready, row, col, value, ?_, nm, rm, rr⟩
  intro r notIndex notRow notCol
  exact (stable r notIndex notRow notCol).trans (fixed r notRow notCol)

end VehicleRoutingSurvey.Routing
end RppSource_PrimOffsetDecode

/-! runtime/PrimPairOutput.lean -/
section RppSource_PrimPairOutput
namespace VehicleRoutingSurvey.Routing

/-- Two natural cells per selected pair, in selection order. -/
structure PrimPairOutputFrame (I : Service) (base : ℕ) (pairs : List (PrimPair I))
    (s : ArithmeticState) : Prop where
  baseAt : s.nr 43 = base
  cursor : s.nr 38 = base + 2 * pairs.length
  length : s.nr 39 = pairs.length
  words : ∀ i : Fin pairs.length,
    s.nm (base + 2 * i.val) = (pairs.get i).1.val ∧
    s.nm (base + 2 * i.val + 1) = (pairs.get i).2.val

def appendPrimPairBlock : List ArithmeticInstruction :=
  [.natStore 38 44, .natAdd 38 38 6, .natStore 38 45, .natAdd 38 38 6, .natAdd 39 39 6]

private def appendPrimPairState (s : ArithmeticState) : ArithmeticState :=
  let cursor := s.nr 38
  let one := s.nr 6
  {s with
    pc := 5
    nr := Function.update (Function.update s.nr 38 (cursor + one + one)) 39 (s.nr 39 + one)
    nm := Function.update (Function.update s.nm cursor (s.nr 44)) (cursor + one) (s.nr 45)}

theorem appendPrimPairBlock_correct {I : Service} {base : ℕ} {pairs : List (PrimPair I)}
    {s : ArithmeticState} (frame : PrimPairOutputFrame I base pairs s)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (pair : PrimPair I) (source : s.nr 44 = pair.1.val) (target : s.nr 45 = pair.2.val) :
    ∃ t, BlockRuns appendPrimPairBlock 5 s t ∧ t.halted = false ∧
      PrimPairOutputFrame I base (pairs ++ [pair]) t ∧
      (∀ r, r ≠ 38 → r ≠ 39 → t.nr r = s.nr r) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ k, k ≠ s.nr 38 → k ≠ s.nr 38 + 1 → t.nm k = s.nm k := by
  let t := appendPrimPairState s
  have runs : BlockRuns appendPrimPairBlock 5 s t := by
    refine ⟨?_, ?_, rfl⟩
    · intro i hi
      interval_cases i <;> simp [appendPrimPairBlock, arithmeticStep, entry, running,
        Function.iterate_succ_apply']
    · simp [t, appendPrimPairState, appendPrimPairBlock, arithmeticStep, entry, running,
        Function.iterate_succ_apply', Function.update_idem]
  have fixed (r : ℕ) (before : r ≠ 38) (size : r ≠ 39) : t.nr r = s.nr r := by
    simp [t, appendPrimPairState, Function.update_of_ne before, Function.update_of_ne size]
  have natural (k : ℕ) (first : k ≠ s.nr 38) (second : k ≠ s.nr 38 + 1) :
      t.nm k = s.nm k := by
    simp [t, appendPrimPairState, one, Function.update_of_ne first, Function.update_of_ne second]
  have newFrame : PrimPairOutputFrame I base (pairs ++ [pair]) t := by
    refine ⟨(fixed 43 (by decide) (by decide)).trans frame.baseAt, ?_, ?_, ?_⟩
    · simp [t, appendPrimPairState, one, frame.cursor] <;> omega
    · simp [t, appendPrimPairState, one, frame.length]
    · intro i
      by_cases previous : i.val < pairs.length
      · have before : base + 2 * i.val + 1 < s.nr 38 := by
          rw [frame.cursor]
          omega
        have same : (pairs ++ [pair]).get i = pairs.get ⟨i.val, previous⟩ := by
          simp only [List.get_eq_getElem, List.getElem_append_left previous]
        rw [same]
        exact ⟨(natural _ (by omega) (by omega)).trans (frame.words ⟨i.val, previous⟩).1,
          (natural _ (by omega) (by omega)).trans (frame.words ⟨i.val, previous⟩).2⟩
      · have atEnd : i.val = pairs.length := by
          have bound := i.isLt
          simp only [List.length_append, List.length_cons, List.length_nil] at bound
          omega
        have past : pairs.length ≤ i.val := by omega
        have same : (pairs ++ [pair]).get i = pair := by
          simp [List.get_eq_getElem, List.getElem_append_right past, atEnd]
        rw [same, atEnd, ← frame.cursor]
        constructor
        · have different : s.nr 38 ≠ s.nr 38 + 1 := by omega
          simp [t, appendPrimPairState, one, Function.update_of_ne different, source]
        · simp [t, appendPrimPairState, one, target]
  exact ⟨t, runs, running, newFrame, fixed, rfl, rfl, natural⟩

def primPairOutputInterface : List ArithmeticInstruction :=
  [.natAdd 34 43 33, .natAdd 35 39 33]

theorem primPairOutputInterface_correct {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 33 = 0) :
    ∃ t, BlockRuns primPairOutputInterface 2 s t ∧ t.halted = false ∧
      t.nr 34 = s.nr 43 ∧ t.nr 35 = s.nr 39 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ≠ 34 → r ≠ 35 → t.nr r = s.nr r := by
  let t := {s with pc := 2, nr := Function.update (Function.update s.nr 34 (s.nr 43)) 35 (s.nr 39)}
  refine ⟨t, ⟨?_, ?_, rfl⟩, running, by simp [t], by simp [t], rfl, rfl, rfl, ?_⟩
  · intro i hi
    interval_cases i <;> simp [primPairOutputInterface, arithmeticStep, entry, running]
  · simp [t, primPairOutputInterface, arithmeticStep, entry, running, Function.iterate_succ_apply', zero]
  · intro r first second
    simp [t, Function.update_of_ne first, Function.update_of_ne second]

end VehicleRoutingSurvey.Routing
end RppSource_PrimPairOutput

/-! runtime/PrimMark.lean -/
section RppSource_PrimMark
namespace VehicleRoutingSurvey.Routing

private theorem required_of_sameComponent {I : Service} {u v : Fin I.graph.n}
    (linked : sameComponent I u v) (needed : u ∈ requiredVertices I) : v ∈ requiredVertices I := by
  induction linked with
  | refl => exact needed
  | tail _ last _ => exact (requiredAdjacent_mem_requiredVertices last).2

open Classical in
theorem markPrimComponent_flag {I : Service} (visited : Finset (RequiredComponent I))
    (labels flags : Fin I.graph.n → ℕ)
    (labelSpec : ∀ u v, labels u = labels v ↔ sameComponent I u v)
    (flagSpec : ∀ u, flags u = if u ∈ requiredVertices I ∧ requiredComponent I u ∈ visited then 1 else 0)
    (target : Fin I.graph.n) (needed : target ∈ requiredVertices I) (u : Fin I.graph.n) :
    (if labels u = labels target then 1 else flags u) =
      if u ∈ requiredVertices I ∧ requiredComponent I u ∈ insert (requiredComponent I target) visited
      then 1 else 0 := by
  by_cases equal : labels u = labels target
  · have same := requiredComponent_eq_iff.mpr ((labelSpec u target).mp equal)
    have included := required_of_sameComponent (requiredComponent_eq_iff.mp same.symm) needed
    rw [if_pos equal, if_pos ⟨included, Finset.mem_insert.mpr (.inl same)⟩]
  · have different : requiredComponent I u ≠ requiredComponent I target :=
      fun same => equal ((labelSpec u target).mpr (requiredComponent_eq_iff.mp same))
    rw [if_neg equal, flagSpec]
    simp [Finset.mem_insert, different]

private def markPrimComponentCell : List ArithmeticInstruction :=
  [.natAdd 44 24 7, .natLoad 45 44, .natSub 46 45 52, .natSub 47 52 45,
    .natAdd 46 46 47, .natAdd 44 41 7, .natBranch 46 33 8 7, .jump 9, .natStore 44 6]

private theorem markPrimComponentCell_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1) (zero : s.nr 33 = 0) :
    ∃ t, BlockRuns markPrimComponentCell 8 s t ∧ t.halted = false ∧
      (∀ r, r < 44 ∨ 47 < r → t.nr r = s.nr r) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      t.nm = Function.update s.nm (s.nr 41 + s.nr 7)
        (if s.nm (s.nr 24 + s.nr 7) = s.nr 52 then 1 else s.nm (s.nr 41 + s.nr 7)) := by
  let labelAddress := s.nr 24 + s.nr 7
  let label := s.nm labelAddress
  let address := s.nr 41 + s.nr 7
  let difference := (label - s.nr 52) + (s.nr 52 - label)
  let read := Function.update (Function.update s.nr 44 labelAddress) 45 label
  let compared := Function.update (Function.update read 46 (label - s.nr 52)) 47 (s.nr 52 - label)
  let registers := Function.update (Function.update compared 46 difference) 44 address
  let middle := {s with pc := 6, nr := registers}
  let t := {s with
    pc := 9
    nr := registers
    nm := Function.update s.nm address (if label = s.nr 52 then 1 else s.nm address)}
  have prep : (arithmeticStep markPrimComponentCell)^[6] s = middle := by
    simp [middle, registers, compared, read, label, labelAddress, address, difference,
      markPrimComponentCell, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have condition : middle.nr 46 ≤ middle.nr 33 ↔ label = s.nr 52 := by
    simp [middle, registers, compared, read, difference, zero] <;> omega
  have branch : arithmeticStep markPrimComponentCell middle =
      {middle with pc := if label = s.nr 52 then 8 else 7} := by
    have live : middle.halted = false := running
    have atTest : middle.pc = 6 := rfl
    simp [arithmeticStep, markPrimComponentCell, live, atTest, condition]
  have execution : BlockRuns markPrimComponentCell 8 s t := by
    refine ⟨?_, ?_, rfl⟩
    · intro i hi
      by_cases earlier : i < 7
      · interval_cases i <;>
          simp [markPrimComponentCell, arithmeticStep, entry, running, Function.iterate_succ_apply']
      · have seventh : i = 7 := by omega
        subst i
        rw [show (7 : ℕ) = 6 + 1 by decide, Function.iterate_succ_apply', prep, branch]
        change (if label = s.nr 52 then 8 else 7) < 9
        split <;> decide
    · rw [show (8 : ℕ) = 2 + 6 by decide, Function.iterate_add_apply, prep]
      rw [show (arithmeticStep markPrimComponentCell)^[2] middle =
        arithmeticStep markPrimComponentCell (arithmeticStep markPrimComponentCell middle) by rfl, branch]
      by_cases equal : label = s.nr 52
      · rw [if_pos equal]
        simp [t, middle, registers, compared, read, markPrimComponentCell, arithmeticStep, running,
          if_pos equal, one]
      · rw [if_neg equal]
        simp [t, middle, markPrimComponentCell, arithmeticStep, running, if_neg equal, Function.update_eq_self]
  refine ⟨t, execution, running, ?_, rfl, rfl, rfl⟩
  intro r limited
  simp [t, registers, compared, read, Function.update_of_ne (show r ≠ 44 by omega),
    Function.update_of_ne (show r ≠ 45 by omega), Function.update_of_ne (show r ≠ 46 by omega),
    Function.update_of_ne (show r ≠ 47 by omega)]

def markPrimComponentLoop : List ArithmeticInstruction :=
  countedLoopFromZero 6 7 5 markPrimComponentCell

private def markVisitedMemory (labels visits targetLabel : ℕ) (count : ℕ) (memory : ℕ → ℕ) :
    ℕ → ℕ :=
  fun k => if visits ≤ k ∧ k < visits + count then
    if memory (labels + (k - visits)) = targetLabel then 1 else memory k
  else memory k

private structure MarkComponentState (initial : ArithmeticState)
    (labels visits target i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 7 = i
  fixed : ∀ r, r ≠ 7 → r < 44 ∨ 47 < r → s.nr r = initial.nr r
  rm : s.rm = initial.rm
  rr : s.rr = initial.rr
  memory : s.nm = markVisitedMemory labels visits target i initial.nm

/-- Mark all vertices with one saved label and preserve every other
memory cell. The label array lies below the visited array. -/
theorem markPrimComponentLoop_correct {s : ArithmeticState} {n labels visits target : ℕ}
    (entry : s.pc = 0) (running : s.halted = false) (count : s.nr 5 = n)
    (one : s.nr 6 = 1) (zero : s.nr 33 = 0) (labelBase : s.nr 24 = labels)
    (visitedBase : s.nr 41 = visits) (targetLabel : s.nr 52 = target)
    (layout : labels + n ≤ visits) :
    ∃ t, BlockRuns markPrimComponentLoop (11 * n + 2) s t ∧ t.halted = false ∧
      (∀ r, r ≠ 7 → r < 44 ∨ 47 < r → t.nr r = s.nr r) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      t.nm = markVisitedMemory labels visits target n s.nm := by
  let inv := MarkComponentState s labels visits target
  let first := {s with pc := 0, nr := Function.update s.nr 7 0}
  have initialization : inv 0 first := by
    refine ⟨rfl, running, by simp [first], ?_, rfl, rfl, ?_⟩
    · intro r different _
      simp [first, Function.update_of_ne different]
    · funext k
      simp [markVisitedMemory, first]
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 5 = n :=
    ⟨hm.entry, hm.running, hm.index, (hm.fixed 5 (by decide) (by decide)).trans count⟩
  have iterate (i : ℕ) (hi : i < n) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns markPrimComponentCell 8 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)} := by
    have oneAt := (hm.fixed 6 (by decide) (by decide)).trans one
    have zeroAt := (hm.fixed 33 (by decide) (by decide)).trans zero
    have labelsAt := (hm.fixed 24 (by decide) (by decide)).trans labelBase
    have visitsAt := (hm.fixed 41 (by decide) (by decide)).trans visitedBase
    have targetAt := (hm.fixed 52 (by decide) (by decide)).trans targetLabel
    obtain ⟨t, run, ready, fixed, rm, rr, nm⟩ :=
      markPrimComponentCell_correct hm.entry hm.running oneAt zeroAt
    have labelRead : m.nm (labels + i) = s.nm (labels + i) := by
      rw [hm.memory, markVisitedMemory, if_neg (by omega)]
    have flagRead : m.nm (visits + i) = s.nm (visits + i) := by
      rw [hm.memory, markVisitedMemory, if_neg (by omega)]
    refine ⟨t, run, ready, rfl, ready, ?_, ?_, rm.trans hm.rm, rr.trans hm.rr, ?_⟩
    · simp [fixed 7 (by decide), fixed 6 (by decide), hm.index, oneAt]
    · intro r different left
      change Function.update t.nr 7 (t.nr 7 + t.nr 6) r = s.nr r
      rw [Function.update_of_ne different, fixed r left, hm.fixed r different left]
    · change t.nm = _
      rw [nm, labelsAt, visitsAt, targetAt, hm.index, labelRead, flagRead]
      funext k
      by_cases address : k = visits + i
      · subst k
        have within : visits ≤ visits + i ∧ visits + i < visits + (i + 1) := by omega
        rw [Function.update_self, markVisitedMemory, if_pos within]
        simp
      · rw [Function.update_of_ne address, hm.memory]
        have same : (visits ≤ k ∧ k < visits + (i + 1)) ↔ (visits ≤ k ∧ k < visits + i) := by omega
        simp only [markVisitedMemory, same]
  obtain ⟨last, complete, run⟩ :=
    countedLoopFromZero_correct 6 7 5 n 8 markPrimComponentCell inv entry running initialization control iterate
  let finish := relocateState 1 {last with pc := (countedLoop 6 7 5 markPrimComponentCell).length}
  have ticks : 1 + (n * (8 + 3) + 1) = 11 * n + 2 := by omega
  exact ⟨finish, by simpa only [markPrimComponentLoop, ticks] using run,
    complete.running, complete.fixed, complete.rm, complete.rr, complete.memory⟩

private def loadPrimTargetLabel : List ArithmeticInstruction :=
  [.natAdd 44 24 45, .natLoad 52 44]

def markPrimTargetBlock : List ArithmeticInstruction :=
  appendBlock loadPrimTargetLabel markPrimComponentLoop

theorem markPrimTargetBlock_correct {s : ArithmeticState} {n labels visits : ℕ}
    (entry : s.pc = 0) (running : s.halted = false) (count : s.nr 5 = n)
    (one : s.nr 6 = 1) (zero : s.nr 33 = 0) (labelBase : s.nr 24 = labels)
    (visitedBase : s.nr 41 = visits) (target : Fin n) (targetAt : s.nr 45 = target.val)
    (layout : labels + n ≤ visits) :
    ∃ t, BlockRuns markPrimTargetBlock (11 * n + 4) s t ∧ t.halted = false ∧
      (∀ r, r ≠ 7 → r ≠ 52 → (r < 44 ∨ 47 < r) → t.nr r = s.nr r) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ k, ¬(visits ≤ k ∧ k < visits + n) → t.nm k = s.nm k) ∧
      ∀ w : Fin n, t.nm (visits + w.val) =
        if s.nm (labels + w.val) = s.nm (labels + target.val) then 1 else s.nm (visits + w.val) := by
  let loaded := {s with
    pc := 2
    nr := Function.update (Function.update s.nr 44 (labels + target.val)) 52
      (s.nm (labels + target.val))}
  have load : BlockRuns loadPrimTargetLabel 2 s loaded := by
    refine ⟨?_, ?_, rfl⟩
    · intro i hi
      interval_cases i <;> simp [loadPrimTargetLabel, arithmeticStep, entry, running]
    · simp [loaded, loadPrimTargetLabel, arithmeticStep, entry, running,
        Function.iterate_succ_apply', labelBase, targetAt]
  let ready := {loaded with pc := 0}
  obtain ⟨marked, run, live, fixed, rm, rr, nm⟩ := markPrimComponentLoop_correct
    (s := ready) (target := s.nm (labels + target.val))
    rfl running count one zero labelBase visitedBase (by simp [ready, loaded]) layout
  let finish := relocateState loadPrimTargetLabel.length marked
  have ticks : 2 + (11 * n + 2) = 11 * n + 4 := by omega
  refine ⟨finish, by simpa only [markPrimTargetBlock, ticks] using load.append run,
    live, ?_, rm, rr, ?_, ?_⟩
  · intro r index notTarget scratch
    have lower := fixed r index scratch
    change marked.nr r = s.nr r
    simpa [ready, loaded, Function.update_of_ne (show r ≠ 44 by omega),
      Function.update_of_ne notTarget] using lower
  · intro k outside
    change marked.nm k = s.nm k
    rw [nm, markVisitedMemory, if_neg outside]
  · intro w
    change marked.nm _ = _
    have bounds : visits ≤ visits + w.val ∧ visits + w.val < visits + n :=
      ⟨Nat.le_add_right _ _, Nat.add_lt_add_left w.isLt _⟩
    simp [nm, markVisitedMemory, bounds, ready, loaded]

end VehicleRoutingSurvey.Routing
end RppSource_PrimMark

/-! runtime/PrimCommit.lean -/
section RppSource_PrimCommit
namespace VehicleRoutingSurvey.Routing

def commitPrimOffsetBlock : List ArithmeticInstruction :=
  appendBlock primOffsetDecodeBlock (appendBlock appendPrimPairBlock markPrimTargetBlock)

/-- Decode and append the chosen pair, then mark its target's component.
The two writes use only the output array, and marking uses only visited flags. -/
theorem commitPrimOffsetBlock_correct {I : Service} {base labels visits : ℕ} {pairs : List (PrimPair I)}
    {s : ArithmeticState} (output : PrimPairOutputFrame I base pairs s)
    (entry : s.pc = 0) (running : s.halted = false) (count : s.nr 5 = I.graph.n)
    (one : s.nr 6 = 1) (zero : s.nr 33 = 0)
    (labelBase : s.nr 24 = labels) (visitedBase : s.nr 41 = visits)
    (labelLayout : labels + I.graph.n ≤ visits) (visitLayout : visits + I.graph.n ≤ base)
    (p : PrimPair I) (selected : s.nr 12 = primPairOffset p) :
    ∃ t, BlockRuns commitPrimOffsetBlock (17 * I.graph.n + 13) s t ∧ t.halted = false ∧
      PrimPairOutputFrame I base (pairs ++ [p]) t ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r < 44, r ≠ 7 → r ≠ 38 → r ≠ 39 → t.nr r = s.nr r) ∧
      (∀ k < base, ¬(visits ≤ k ∧ k < visits + I.graph.n) → t.nm k = s.nm k) ∧
      ∀ w : Fin I.graph.n, t.nm (visits + w.val) =
        if s.nm (labels + w.val) = s.nm (labels + p.2.val) then 1 else s.nm (visits + w.val) := by
  have valid : s.nr 12 < I.graph.n ^ 2 := by
    rw [selected]
    exact primPairOffset_lt p
  obtain ⟨decoded, q, decode, decodeReady, sourceAt, targetAt, offset, decodeFixed, decodeNm,
    decodeRm, decodeRr⟩ := primOffsetDecodeBlock_correct entry running count one zero valid
  have same : q = p := primPairOffset_injective (offset.trans selected)
  subst q
  let writing := {decoded with pc := 0}
  have currentOutput : PrimPairOutputFrame I base pairs writing :=
    ⟨(decodeFixed 43 (by decide) (by decide) (by decide)).trans output.baseAt,
      (decodeFixed 38 (by decide) (by decide) (by decide)).trans output.cursor,
      (decodeFixed 39 (by decide) (by decide) (by decide)).trans output.length,
      fun i => ⟨(congrFun decodeNm _).trans (output.words i).1,
        (congrFun decodeNm _).trans (output.words i).2⟩⟩
  have writingOne : writing.nr 6 = 1 := (decodeFixed 6 (by decide) (by decide) (by decide)).trans one
  obtain ⟨appended, store, storeReady, stored, appendFixed, appendRm, appendRr, appendNm⟩ :=
    appendPrimPairBlock_correct currentOutput rfl decodeReady writingOne p sourceAt targetAt
  have inputBelow (k : ℕ) (below : k < base) : appended.nm k = s.nm k := by
    have cursor := currentOutput.cursor
    exact (appendNm k (by omega) (by omega)).trans (congrFun decodeNm _)
  let markStart := {appended with pc := 0}
  have beforeMark (r : ℕ) (r7 : r ≠ 7) (r38 : r ≠ 38) (r39 : r ≠ 39)
      (r44 : r ≠ 44) (r45 : r ≠ 45) : markStart.nr r = s.nr r :=
    (appendFixed r r38 r39).trans (decodeFixed r r7 r44 r45)
  have targetStill : markStart.nr 45 = p.2.val :=
    (appendFixed 45 (by decide) (by decide)).trans targetAt
  obtain ⟨marked, mark, markReady, markFixed, markRm, markRr, markKeeps, markFlags⟩ :=
    markPrimTargetBlock_correct (s := markStart) rfl storeReady
      ((beforeMark 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans count)
      ((beforeMark 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans one)
      ((beforeMark 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans zero)
      ((beforeMark 24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans labelBase)
      ((beforeMark 41 (by decide) (by decide) (by decide) (by decide) (by decide)).trans visitedBase)
      p.2 targetStill labelLayout
  let finish := relocateState primOffsetDecodeBlock.length (relocateState appendPrimPairBlock.length marked)
  have finalOutput : PrimPairOutputFrame I base (pairs ++ [p]) finish :=
    ⟨(markFixed 43 (by decide) (by decide) (by decide)).trans stored.baseAt,
      (markFixed 38 (by decide) (by decide) (by decide)).trans stored.cursor,
      (markFixed 39 (by decide) (by decide) (by decide)).trans stored.length, fun i =>
        ⟨(markKeeps _ (by omega)).trans (stored.words i).1,
          (markKeeps _ (by omega)).trans (stored.words i).2⟩⟩
  have ticks : (6 * I.graph.n + 4) + (5 + (11 * I.graph.n + 4)) = 17 * I.graph.n + 13 := by omega
  refine ⟨finish, by simpa only [commitPrimOffsetBlock, ticks] using decode.append (store.append mark),
    markReady, finalOutput, (markRm.trans appendRm).trans decodeRm, (markRr.trans appendRr).trans decodeRr,
    ?_, ?_, ?_⟩
  · intro r low index cursor size
    exact (markFixed r index (by omega) (.inl low)).trans
      (beforeMark r index cursor size (by omega) (by omega))
  · intro k below outside
    exact (markKeeps k outside).trans (inputBelow k below)
  · intro w
    change marked.nm _ = _
    rw [markFlags]
    change (if appended.nm (labels + w.val) = appended.nm (labels + p.2.val)
      then 1 else appended.nm (visits + w.val)) = _
    rw [inputBelow _ (by have bound := w.isLt; omega), inputBelow _ (by have bound := p.2.isLt; omega),
      inputBelow _ (by have bound := w.isLt; omega)]

end VehicleRoutingSurvey.Routing
end RppSource_PrimCommit


