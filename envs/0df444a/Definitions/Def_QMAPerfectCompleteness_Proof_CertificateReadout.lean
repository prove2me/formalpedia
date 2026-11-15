-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
-- name    : QMAPerfectCompleteness_Proof_CertificateReadout
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:57:03.292839+00:00
-- url     : https://prove2.me/theorems/dc95d911-03e0-4832-a58f-e8376dbe49b8
-- title:
--   Clean zero-test and validity-controlled acceptance flag
-- statement:
--   Defines a reversible zero test for a selected register and a validity-controlled update of the acceptance output. With the test bit and scratch initially clean, the output is XORed with the conjunction of validity and a nonzero tested register; reversing the zero-test restores its temporary bit and scratch.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateReadout.lean, lines 10–80.

/- Generated from Solutions.CertificateReadout by authoritative Stage-2 skeleton subtraction.
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



/-! A literal final acceptance flag for the coherent certificate verifier: valid AND Z≠0.
The zero-test work bit and every shared scratch flag are restored. -/
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateReadout
open ReversibleGadgets ControlCircuits EqualityCircuits BooleanCircuits BlockCompiler

structure Layout (r n : ℕ) where
  zeros : AndLayout r n
  tags : Fin 3 ↪ Fin n
  disjoint_controls : ∀ i j, tags i ≠ zeros.controls j
  disjoint_flags : ∀ i j, tags i ≠ zeros.flags j

namespace Layout
variable {r n : ℕ} (L : Layout r n)
abbrev valid := L.tags 0
abbrev zero := L.tags 1
abbrev output := L.tags 2

def Clean (x : Basis n) : Prop := ∀ j, x (L.zeros.flags j) = false

def allZero (x : Basis n) : Prop := ∀ j, x (L.zeros.controls j) = false
instance (x : Basis n) : Decidable (L.allZero x) := inferInstanceAs (Decidable (∀ j, _))

def zeroAction (x : Basis n) : Basis n := Function.update x L.zero (xor (x L.zero) (decide (L.allZero x)))

noncomputable def zeroProgram : CleanProgram n L.Clean where
  gates := patternControlledX L.zeros (fun _ => false) L.zero (L.disjoint_flags 1)
  action := L.zeroAction
  sound y x hx := patternControlledX_matrix L.zeros (fun _ => false) L.zero
    (L.disjoint_controls 1) (L.disjoint_flags 1) y x hx
  preserves x hx := by
    intro j
    rw [zeroAction,Function.update_of_ne (L.disjoint_flags 1 j).symm]
    exact hx j

lemma allZero_update (x : Basis n) (i : Fin 3) (b : Bool) :
    L.allZero (Function.update x (L.tags i) b) ↔ L.allZero x := by
  simp only [allZero,Function.update_of_ne (L.disjoint_controls i _).symm]

lemma zeroAction_involutive : Function.Involutive L.zeroAction := by
  intro x
  simp [zeroAction,L.allZero_update,Function.update_idem]

def flagCommands : List (Command n) :=
  [.flip L.zero,.conj L.valid L.zero L.output
    (L.tags.injective.ne (by decide)) (L.tags.injective.ne (by decide)),.flip L.zero]

def flagAction (x : Basis n) : Basis n :=
  Function.update x L.output (xor (x L.output) (x L.valid && !x L.zero))

lemma flagCommands_eval (x : Basis n) : eval L.flagCommands x = L.flagAction x := by
  funext w
  by_cases hz : w=L.zero
  · subst w
    simp [flagCommands,eval,evalCommand,flagAction,Function.update_apply,L.tags.injective.eq_iff]
  · by_cases ho : w=L.output
    · subst w
      simp [flagCommands,eval,evalCommand,flagAction,Function.update_apply,L.tags.injective.eq_iff]
    · simp [flagCommands,eval,evalCommand,flagAction,Function.update_apply,hz,ho]

noncomputable def flagProgram : CleanProgram n L.Clean where
  gates := compile L.flagCommands
  action := L.flagAction
  sound y x hx := by
    rw [compile_matrix]
    change (if y = eval L.flagCommands x then (1 : ℂ) else 0) = _
    rw [L.flagCommands_eval]
  preserves x hx := by
    intro j
    rw [flagAction,Function.update_of_ne (L.disjoint_flags 2 j).symm]
    exact hx j

noncomputable def program : CleanProgram n L.Clean :=
  (L.zeroProgram.append L.flagProgram).append
    (L.zeroProgram.reverseOfInvolution L.zeroAction_involutive)

noncomputable def gates : List (Instr gatesG2 n) := L.program.gates







end Layout
end QMAPerfectCompleteness.Main.CertificateReadout


