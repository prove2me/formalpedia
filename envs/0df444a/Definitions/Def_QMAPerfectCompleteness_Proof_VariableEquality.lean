-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
-- name    : QMAPerfectCompleteness_Proof_VariableEquality
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:02:38.512092+00:00
-- url     : https://prove2.me/theorems/33824a66-71ac-4987-9cc8-2766641bd6fd
-- title:
--   Clean equality of variable binary registers
-- statement:
--   Defines an equality test from two variable-register comparisons, input swapping and clean tag combination. The resulting reversible program flips the equality flag and restores the borrowed comparison workspace.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/VariableEquality.lean, retained declaration span lines 10–144.

/- Generated from Solutions.VariableEquality by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison



/-! A clean equality test on two variable binary registers, using two linear comparators. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.VariableEquality
open VariableComparison ComparisonCircuits BlockCompiler ReversibleGadgets

/-- Swap source words while leaving the reusable borrow workspace in place. -/
def swapIndex (r : ℕ) (j : Fin (3*r+2)) : Fin (3*r+2) :=
  ⟨if j.val<r then r+j.val else if j.val<2*r then j.val-r else j.val,by
    have := j.isLt
    split_ifs <;> omega⟩
lemma swapIndex_involutive (r : ℕ) : Function.Involutive (swapIndex r) := by
  intro j
  apply Fin.ext
  dsimp [swapIndex]
  split_ifs <;> omega

def swapInputs {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) : Fin (3*r+2) ↪ Fin n :=
  ⟨fun j => e (swapIndex r j),fun i j h => (swapIndex_involutive r).injective (e.injective h)⟩

@[simp] lemma swap_left {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (i : Fin r) :
    leftWire (swapInputs e) i = rightWire e i := by
  apply congrArg e
  apply Fin.ext
  simp [leftWire,rightWire,swapInputs,swapIndex,i.isLt]
@[simp] lemma swap_right {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (i : Fin r) :
    rightWire (swapInputs e) i = leftWire e i := by
  apply congrArg e
  apply Fin.ext
  have hi := i.isLt
  simp [leftWire,rightWire,swapInputs,swapIndex,show ¬r+i.val<r by omega,show r+i.val<2*r by omega]
@[simp] lemma swap_carry {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (i : Fin (r+1)) :
    carryWire (swapInputs e) i = carryWire e i := by
  apply congrArg e
  apply Fin.ext
  simp [carryWire,swapInputs,swapIndex,show ¬2*r+i.val<r by omega,show ¬2*r+i.val<2*r by omega]
@[simp] lemma swap_temp {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) :
    tempWire (swapInputs e) = tempWire e := by
  apply congrArg e
  apply Fin.ext
  simp [tempWire,swapInputs,swapIndex,show ¬3*r+1<r by omega,show ¬3*r+1<2*r by omega]

def Clean {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (x : Basis n) : Prop :=
  (∀ j, x (carryWire e j) = false) ∧ x (tempWire e) = false

def comparisonBit {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (x : Basis n) : Bool :=
  decide (littleValue (x ∘ leftWire e) < littleValue (x ∘ rightWire e))

lemma comparisonBit_update {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) (x : Basis n)
    (w : Fin n) (b : Bool) (hw : ∀ j, w ≠ e j) :
    comparisonBit e (Function.update x w b) = comparisonBit e x := by
  have hl : (Function.update x w b) ∘ leftWire e = x ∘ leftWire e := by
    funext j; exact Function.update_of_ne (hw _).symm _ _
  have hr : (Function.update x w b) ∘ rightWire e = x ∘ rightWire e := by
    funext j; exact Function.update_of_ne (hw _).symm _ _
  unfold comparisonBit
  rw [hl,hr]

noncomputable def comparisonProgram {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n)
    (target : Fin n) (hout : ∀ j, target ≠ e j) : CleanProgram n (Clean e) where
  gates := comparatorGates e target hout
  action x := Function.update x target (xor (x target) (comparisonBit e x))
  sound y x hx := comparatorGates_matrix e target hout y x hx.1 hx.2
  preserves x hx := by
    constructor
    · intro j
      rw [Function.update_of_ne (show carryWire e j ≠ target from (hout _).symm)]
      exact hx.1 j
    · rw [Function.update_of_ne (show tempWire e ≠ target from (hout _).symm)]
      exact hx.2

noncomputable def swappedProgram {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n)
    (target : Fin n) (hout : ∀ j, target ≠ e j) : CleanProgram n (Clean e) where
  gates := comparatorGates (swapInputs e) target (fun j => hout _)
  action x := Function.update x target (xor (x target) (comparisonBit (swapInputs e) x))
  sound y x hx := by
    apply comparatorGates_matrix
    · simpa using hx.1
    · simpa using hx.2
  preserves x hx := by
    constructor
    · intro j
      rw [Function.update_of_ne (show carryWire e j ≠ target from (hout _).symm)]
      exact hx.1 j
    · rw [Function.update_of_ne (show tempWire e ≠ target from (hout _).symm)]
      exact hx.2

noncomputable def flipProgram {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n)
    (target : Fin n) (hout : ∀ j, target ≠ e j) : CleanProgram n (Clean e) where
  gates := [xAt target]
  action := xAction target
  sound y x hx := by simp only [circuitMatrix,Matrix.one_mul,xAt_matrix]; rfl
  preserves x hx := by
    constructor
    · intro j
      rw [xAction,Function.update_of_ne (show carryWire e j ≠ target from (hout _).symm)]
      exact hx.1 j
    · rw [xAction,Function.update_of_ne (show tempWire e ≠ target from (hout _).symm)]
      exact hx.2

noncomputable def program {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n)
    (target : Fin n) (hout : ∀ j, target ≠ e j) : CleanProgram n (Clean e) :=
  ((comparisonProgram e target hout).append (swappedProgram e target hout)).append
    (flipProgram e target hout)

lemma program_action {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n)
    (target : Fin n) (hout : ∀ j, target ≠ e j) (x : Basis n) :
    (program e target hout).action x = Function.update x target (xor (x target)
      (decide (littleValue (x ∘ leftWire e) = littleValue (x ∘ rightWire e)))) := by
  have hs : comparisonBit (swapInputs e) x =
      decide (littleValue (x ∘ rightWire e) < littleValue (x ∘ leftWire e)) := by
    simp [comparisonBit,Function.comp_def]
  simp only [program,CleanProgram.append,comparisonProgram,swappedProgram,flipProgram,
    Function.comp_apply,xAction,comparisonBit_update _ _ _ _ (fun j => hout _),Function.update_self,Function.update_idem]
  congr 1
  rw [comparisonBit_update (swapInputs e) x target _ (fun j => hout _),hs]
  unfold comparisonBit
  rcases lt_trichotomy (littleValue (x ∘ leftWire e)) (littleValue (x ∘ rightWire e)) with h|h|h
  · simp [h,show ¬littleValue (x ∘ rightWire e)<littleValue (x ∘ leftWire e) by omega,ne_of_lt h]
  · simp [h]
  · simp [h,show ¬littleValue (x ∘ leftWire e)<littleValue (x ∘ rightWire e) by omega,ne_of_gt h]

/-- Equality of little-endian integers is exactly equality of their bit strings. -/
lemma littleValue_eq_iff {r : ℕ} (a b : Fin r → Bool) : littleValue a = littleValue b ↔ a=b := by
  constructor
  · intro h
    funext j
    have hb := congrArg (fun v : ℕ => v.testBit j.val) h
    simpa only [ClockCircuits.littleValue_decode] using hb
  · rintro rfl; rfl

noncomputable def gates {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n)
    (target : Fin n) (hout : ∀ j, target ≠ e j) := (program e target hout).gates

/-- Exact clean variable equality, with every data and workspace wire restored. -/
theorem gates_matrix {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n)
    (target : Fin n) (hout : ∀ j, target ≠ e j) (y x : Basis n) (hx : Clean e x) :
    circuitMatrix (gates e target hout) y x = if y = Function.update x target
      (xor (x target) (decide ((x ∘ leftWire e) = (x ∘ rightWire e)))) then 1 else 0 := by
  rw [gates,(program e target hout).sound y x hx,program_action]
  simp only [littleValue_eq_iff]



end QMAPerfectCompleteness.Main.VariableEquality


