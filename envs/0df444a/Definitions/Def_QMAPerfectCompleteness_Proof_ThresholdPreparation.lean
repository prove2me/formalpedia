-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
-- name    : QMAPerfectCompleteness_Proof_ThresholdPreparation
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:59:06.150342+00:00
-- url     : https://prove2.me/theorems/62636614-392e-48b4-9d6c-921b09021895
-- title:
--   Preparing padded certificate arithmetic words
-- statement:
--   Defines the physical register layout and literal copy/addition commands for the six words A, 2A, B, 2B, 3A and 3A+B. The certificate inputs are retained, while the explicit carry and temporary registers support reversible threshold preparation.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, Section 3.3, the coherent-certificate verifier and controlled block construction. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ThresholdPreparation.lean, retained declaration span lines 10–306.

/- Generated from Solutions.ThresholdPreparation by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition



/-! Certificate-dependent binary threshold preparation. Arithmetic registers are explicit
physical wires; their values may be retained as certificate-dependent ancillary garbage. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.ThresholdPreparation
open BooleanCircuits ComparisonCircuits

inductive Slot (k : ℕ) where
  | certificate : Fin 2 → Fin k → Slot k
  | word : Fin 6 → Fin (k+2) → Slot k
  | carry : Fin (k+3) → Slot k
  | temp : Slot k
  deriving DecidableEq, Fintype

/-- Six padded words A,2A,B,2B,3A,3A+B share one clean carry bank. -/
structure Layout (k n : ℕ) where
  wire : Slot k ↪ Fin n
  three : VariableAddition.Layout (k+2) n
  upper : VariableAddition.Layout (k+2) n
  three_left : ∀ j, three.left j = wire (.word 0 j)
  three_right : ∀ j, three.right j = wire (.word 1 j)
  three_output : ∀ j, three.output j = wire (.word 4 j)
  upper_left : ∀ j, upper.left j = wire (.word 4 j)
  upper_right : ∀ j, upper.right j = wire (.word 2 j)
  upper_output : ∀ j, upper.output j = wire (.word 5 j)
  three_carry : ∀ j, three.carry j = wire (.carry j)
  upper_carry : ∀ j, upper.carry j = wire (.carry j)
  three_temp : three.temp = wire .temp
  upper_temp : upper.temp = wire .temp

namespace Layout
variable {k n : ℕ} (L : Layout k n)

abbrev CopyIndex := Fin 4 × Fin k

def source (i : CopyIndex (k := k)) : Fin n :=
  L.wire (.certificate (if i.1.val < 2 then 0 else 1) i.2)

def targetPosition (i : CopyIndex (k := k)) : Fin (k+2) :=
  ⟨i.2.val+i.1.val%2,by have := i.2.isLt; have := Nat.mod_lt i.1.val (by decide : 0<2); omega⟩

def target (i : CopyIndex (k := k)) : Fin n :=
  L.wire (.word ⟨i.1.val,by have := i.1.isLt; omega⟩ (targetPosition i))

lemma target_injective : Function.Injective L.target := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  have hp := L.wire.injective h
  change Slot.word (⟨i.val,by omega⟩ : Fin 6) (targetPosition (i,j)) =
    Slot.word (⟨i'.val,by omega⟩ : Fin 6) (targetPosition (i',j')) at hp
  obtain ⟨hi,hj⟩ := Slot.word.inj hp
  have hival := congrArg Fin.val hi
  have hijeq : i=i' := Fin.ext hival
  subst i'
  have hjval := congrArg Fin.val hj
  have hjeq : j=j' := Fin.ext (by change j.val+i.val%2=j'.val+i.val%2 at hjval; omega)
  subst j'
  rfl

def targetEmbedding : CopyIndex (k := k) ↪ Fin n := ⟨L.target,L.target_injective⟩

lemma source_ne_target (i j : CopyIndex (k := k)) : L.source i ≠ L.targetEmbedding j := by
  intro h
  have hh := L.wire.injective h
  cases hh

def copyIndices : List (CopyIndex (k := k)) :=
  (List.finRange (4*k)).map finProdFinEquiv.symm





def copies : List (Command n) :=
  RegisterCopies.commands L.source L.targetEmbedding L.source_ne_target copyIndices



def copyState (x : Basis n) : Basis n := eval L.copies x















lemma target_odd (d : Fin 4) (hd : d.val%2=1) (j : Fin k) :
    L.target (d,j) = L.wire (.word ⟨d.val,by have := d.isLt; omega⟩ (Fin.castAdd 1 j).succ) := by
  unfold target
  congr 2
  apply Fin.ext
  exact congrArg (fun v => j.val+v) hd











/-- Copies are followed by two literal clean binary adders. -/
def commands : List (Command n) := L.copies ++ L.three.commands ++ L.upper.commands
noncomputable def gates : List (Instr gatesG2 n) := compile L.commands





















def state (x : Basis n) : Basis n := eval L.commands x







def Clean (x : Basis n) : Prop :=
  (∀ d j, x (L.wire (.word d j)) = false) ∧
    (∀ j, x (L.wire (.carry j)) = false) ∧ x (L.wire .temp) = false

def value (x : Basis n) (d : Fin 2) : ℕ := littleValue (fun j => x (L.wire (.certificate d j)))









end Layout
end QMAPerfectCompleteness.Main.ThresholdPreparation


