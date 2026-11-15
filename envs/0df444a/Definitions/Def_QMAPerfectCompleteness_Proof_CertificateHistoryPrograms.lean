-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryPrograms
-- name    : QMAPerfectCompleteness_Proof_CertificateHistoryPrograms
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:04:50.351241+00:00
-- url     : https://prove2.me/theorems/3f223cd8-5783-43fd-a5a4-5fa66ddd55be
-- title:
--   Clean history predicates and controlled closing programs
-- statement:
--   Packages the conjunction of proof equality with $z$ and the final-clock predicate as a clean reversible program. A closing layout combines that predicate with a range-control bit to XOR the block flag, then reverses the predicate computation so that its temporary flags are restored.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateHistoryPrograms.lean, lines 13–106.

/- Generated from Solutions.CertificateHistoryPrograms by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality



/-! Clean compute/use/uncompute of the variable certificate history predicate. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateHistoryPrograms
open BlockCompiler ReversibleGadgets VariableHistoryEquality

namespace Layout
variable {m c n : ℕ} (L : VariableHistoryEquality.Layout m c n)

def Clean (x : Basis n) : Prop := L.Clean x ∧ x (L.tags 0)=false ∧ x (L.tags 1)=false

def predicate (x : Basis n) : Bool := decide (L.proofMatches x) && decide (L.clockMatches x)
def action (x : Basis n) : Basis n := Function.update x (L.tags 2) (xor (x (L.tags 2)) (predicate L x))

noncomputable def program : CleanProgram n (Clean L) where
  gates := L.gates
  action := action L
  sound y x hx := L.gates_matrix y x hx.1 hx.2.1 hx.2.2
  preserves x hx := by
    refine ⟨L.clean_update x hx.1 2 _,?_,?_⟩
    · rw [action,Function.update_of_ne (L.tags.injective.ne (by decide : (0 : Fin 3) ≠ 2))]
      exact hx.2.1
    · rw [action,Function.update_of_ne (L.tags.injective.ne (by decide : (1 : Fin 3) ≠ 2))]
      exact hx.2.2

lemma action_involutive : Function.Involutive (action L) := by
  intro x
  simp [action,predicate,L.proofMatches_update,L.clockMatches_update,Function.update_idem]

end Layout

structure ClosingLayout (m c n : ℕ) where
  history : VariableHistoryEquality.Layout m c n
  range : Fin n
  flag : Fin n
  range_history : range ≠ history.tags 2
  range_flag : range ≠ flag
  flag_tags : ∀ i, flag ≠ history.tags i
  flag_eq : ∀ i, flag ≠ history.equality i
  flag_clock : ∀ i, flag ≠ history.clock.controls i
  flag_scratch : ∀ i, flag ≠ history.clock.flags i

namespace ClosingLayout
variable {m c n : ℕ} (L : ClosingLayout m c n)

def targets : Fin 3 ↪ Fin n :=
  BooleanCircuits.triple L.range (L.history.tags 2) L.flag L.range_history L.range_flag (L.flag_tags 2).symm



def useAction (x : Basis n) : Basis n :=
  Function.update x L.flag (xor (x L.flag) (x L.range && x (L.history.tags 2)))

noncomputable def useProgram : CleanProgram n (Layout.Clean L.history) where
  gates := [toffoliAt L.targets]
  action := L.useAction
  sound y x _ := by simp only [circuitMatrix,Matrix.one_mul,toffoliAt_matrix]; rfl
  preserves x hx := by
    change Layout.Clean L.history (Function.update x L.flag
      (xor (x L.flag) (x L.range && x (L.history.tags 2))))
    refine ⟨⟨⟨?_,?_⟩,?_⟩,?_,?_⟩
    · intro j
      rw [Function.update_of_ne (show VariableComparison.carryWire L.history.equality j ≠ L.flag from
        (L.flag_eq _).symm)]
      exact hx.1.1.1 j
    · rw [Function.update_of_ne (show VariableComparison.tempWire L.history.equality ≠ L.flag from
        (L.flag_eq _).symm)]
      exact hx.1.1.2
    · intro j
      rw [Function.update_of_ne (L.flag_scratch j).symm]
      exact hx.1.2 j
    · rw [Function.update_of_ne (L.flag_tags 0).symm]
      exact hx.2.1
    · rw [Function.update_of_ne (L.flag_tags 1).symm]
      exact hx.2.2





noncomputable def program : CleanProgram n (Layout.Clean L.history) :=
  ((Layout.program L.history).append L.useProgram).append
    ((Layout.program L.history).reverseOfInvolution (Layout.action_involutive L.history))

noncomputable abbrev action : Basis n → Basis n := L.program.action
noncomputable def gates := L.program.gates









end ClosingLayout
end QMAPerfectCompleteness.Main.CertificateHistoryPrograms


