-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
-- name    : QMAPerfectCompleteness_Proof_VariableHistoryEquality
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:03:29.041221+00:00
-- url     : https://prove2.me/theorems/21cdef1a-b456-4f3b-b7a2-d013f45c774c
-- title:
--   Certificate-dependent history equality controls
-- statement:
--   Defines the coherent test that the clock is at its final binary value and the proof register equals the variable certificate word. Equality and clock-control programs compute the combined condition and restore temporary flags and comparison workspace.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, Section 3.3, the coherent-certificate verifier and controlled block construction. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/VariableHistoryEquality.lean, retained declaration span lines 9–115.

/- Generated from Solutions.VariableHistoryEquality by authoritative Stage-2 skeleton subtraction.
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



/-! A coherent history test: clock all ones and proof equal to the variable certificate z.
All temporary equality flags and comparison workspace are restored. -/
open Matrix
namespace QMAPerfectCompleteness.Main.VariableHistoryEquality
open VariableComparison ReversibleGadgets ControlCircuits EqualityCircuits BlockCompiler

structure Layout (m c n : ℕ) where
  equality : Fin (3*m+2) ↪ Fin n
  clock : AndLayout c n
  tags : Fin 3 ↪ Fin n
  eq_disjoint : ∀ i j, tags i ≠ equality j
  clock_disjoint : ∀ i j, tags i ≠ clock.controls j
  flags_disjoint : ∀ i j, tags i ≠ clock.flags j

namespace Layout
variable {m c n : ℕ} (L : Layout m c n)

def Clean (x : Basis n) : Prop := VariableEquality.Clean L.equality x ∧ ∀j, x (L.clock.flags j)=false

def proofMatches (x : Basis n) : Prop := (x ∘ leftWire L.equality) = (x ∘ rightWire L.equality)
instance (x : Basis n) : Decidable (L.proofMatches x) := inferInstanceAs (Decidable (_ = _))
def clockMatches (x : Basis n) : Prop := ∀j,x (L.clock.controls j)=true
instance (x : Basis n) : Decidable (L.clockMatches x) := inferInstanceAs (Decidable (∀j,_))

lemma proofMatches_update (x : Basis n) (i : Fin 3) (b : Bool) :
    L.proofMatches (Function.update x (L.tags i) b) ↔ L.proofMatches x := by
  have hl : (Function.update x (L.tags i) b) ∘ leftWire L.equality = x ∘ leftWire L.equality := by
    funext j; exact Function.update_of_ne (L.eq_disjoint i _).symm _ _
  have hr : (Function.update x (L.tags i) b) ∘ rightWire L.equality = x ∘ rightWire L.equality := by
    funext j; exact Function.update_of_ne (L.eq_disjoint i _).symm _ _
  unfold proofMatches
  rw [hl,hr]
lemma clockMatches_update (x : Basis n) (i : Fin 3) (b : Bool) :
    L.clockMatches (Function.update x (L.tags i) b) ↔ L.clockMatches x := by
  simp only [clockMatches,Function.update_of_ne (L.clock_disjoint i _).symm]

lemma clean_update (x : Basis n) (hx : L.Clean x) (i : Fin 3) (b : Bool) :
    L.Clean (Function.update x (L.tags i) b) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro j
    rw [Function.update_of_ne (show carryWire L.equality j ≠ L.tags i from (L.eq_disjoint i _).symm)]
    exact hx.1.1 j
  · rw [Function.update_of_ne (show tempWire L.equality ≠ L.tags i from (L.eq_disjoint i _).symm)]
    exact hx.1.2
  · intro j
    rw [Function.update_of_ne (L.flags_disjoint i j).symm]
    exact hx.2 j

def equalityAction (x : Basis n) : Basis n :=
  Function.update x (L.tags 0) (xor (x (L.tags 0)) (decide (L.proofMatches x)))
def clockAction (x : Basis n) : Basis n :=
  Function.update x (L.tags 1) (xor (x (L.tags 1)) (decide (L.clockMatches x)))

noncomputable def equalityProgram : CleanProgram n L.Clean where
  gates := VariableEquality.gates L.equality (L.tags 0) (L.eq_disjoint 0)
  action := L.equalityAction
  sound y x hx := VariableEquality.gates_matrix L.equality (L.tags 0) (L.eq_disjoint 0) y x hx.1
  preserves x hx := L.clean_update x hx 0 _
noncomputable def clockProgram : CleanProgram n L.Clean where
  gates := patternControlledX L.clock (fun _=>true) (L.tags 1) (L.flags_disjoint 1)
  action := L.clockAction
  sound y x hx := patternControlledX_matrix L.clock (fun _=>true) (L.tags 1)
    (L.clock_disjoint 1) (L.flags_disjoint 1) y x hx.2
  preserves x hx := L.clean_update x hx 1 _
noncomputable def useProgram : CleanProgram n L.Clean where
  gates := [toffoliAt L.tags]
  action := toffoliAction L.tags
  sound y x hx := by simp only [circuitMatrix,Matrix.one_mul,toffoliAt_matrix]; rfl
  preserves x hx := L.clean_update x hx 2 _

lemma equalityAction_involutive : Function.Involutive L.equalityAction := by
  intro x
  simp [equalityAction,L.proofMatches_update,Function.update_idem]
lemma clockAction_involutive : Function.Involutive L.clockAction := by
  intro x
  simp [clockAction,L.clockMatches_update,Function.update_idem]

noncomputable def program : CleanProgram n L.Clean :=
  (((L.equalityProgram.append L.clockProgram).append L.useProgram).append
    (L.clockProgram.reverseOfInvolution L.clockAction_involutive)).append
      (L.equalityProgram.reverseOfInvolution L.equalityAction_involutive)

noncomputable def gates := L.program.gates

lemma program_action (x : Basis n) (h0 : x (L.tags 0)=false) (h1 : x (L.tags 1)=false) :
    L.program.action x = Function.update x (L.tags 2) (xor (x (L.tags 2))
      ((decide (L.proofMatches x)) && (decide (L.clockMatches x)))) := by
  funext w
  by_cases hw0 : w=L.tags 0
  · subst w
    simp [program,CleanProgram.append,CleanProgram.reverseOfInvolution,equalityProgram,clockProgram,
      useProgram,Function.comp_apply,equalityAction,clockAction,toffoliAction,L.proofMatches_update,
      L.clockMatches_update,Function.update_apply,L.tags.injective.eq_iff,h0,h1]
  · by_cases hw1 : w=L.tags 1
    · subst w
      simp [program,CleanProgram.append,CleanProgram.reverseOfInvolution,equalityProgram,clockProgram,
        useProgram,Function.comp_apply,equalityAction,clockAction,toffoliAction,L.proofMatches_update,
        L.clockMatches_update,Function.update_apply,L.tags.injective.eq_iff,h0,h1]
    · by_cases hw2 : w=L.tags 2
      · subst w
        simp [program,CleanProgram.append,CleanProgram.reverseOfInvolution,equalityProgram,clockProgram,
          useProgram,Function.comp_apply,equalityAction,clockAction,toffoliAction,L.proofMatches_update,
          L.clockMatches_update,Function.update_apply,L.tags.injective.eq_iff,h0,h1]
      · simp [program,CleanProgram.append,CleanProgram.reverseOfInvolution,equalityProgram,clockProgram,
          useProgram,Function.comp_apply,equalityAction,clockAction,toffoliAction,L.proofMatches_update,
          L.clockMatches_update,Function.update_apply,hw0,hw1,hw2]

/-- Exact matrix of the variable-z and last-clock predicate, with no certificate measurement. -/
theorem gates_matrix (y x : Basis n) (hx : L.Clean x)
    (h0 : x (L.tags 0)=false) (h1 : x (L.tags 1)=false) :
    circuitMatrix L.gates y x = if y=Function.update x (L.tags 2) (xor (x (L.tags 2))
      ((decide (L.proofMatches x)) && (decide (L.clockMatches x)))) then 1 else 0 := by
  rw [gates,L.program.sound y x hx,L.program_action x h0 h1]



end Layout
end QMAPerfectCompleteness.Main.VariableHistoryEquality


