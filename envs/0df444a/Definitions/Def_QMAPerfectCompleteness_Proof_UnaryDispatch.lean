-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_UnaryDispatch
-- name    : QMAPerfectCompleteness_Proof_UnaryDispatch
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:00:29.673217+00:00
-- url     : https://prove2.me/theorems/d9b67f54-f1b0-46da-a036-396dd08d8f75
-- title:
--   Finite selection by a unary tag
-- statement:
--   Defines a finite program that consumes a unary tag and selects the corresponding entry of a fixed program list. Its execution bound adds twice the tag length plus one to the selected body bound, preserving every unrelated stack.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/UnaryDispatch.lean, retained declaration span lines 9–52.

/- Generated from Solutions.UnaryDispatch by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Finite dispatch on a unary counter, consuming that counter and preserving all other stacks. -/
set_option backward.isDefEq.respectTransparency false
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.StructuredStack.Code
variable {K : Type} [DecidableEq K]

def selectUnary (tag : K) (fallback : Code K) : List (Code K) → Code K
  | [] => fallback
  | P::Ps => ifPeek tag Option.isSome (seq (pop tag) (selectUnary tag fallback Ps)) P

lemma selectUnary_exec (tag : K) (fallback : Code K) (g : ℕ) :
    ∀ (choices : List (Code K)) (P : Code K) (hget : choices[g]?=some P)
      (S : K→List Bool) (q : Option Bool) (hTag : S tag=unary g)
      (e : Data K) (t : ℕ)
      (hbody : ∀ q,P.Exec (q,Function.update S tag []) e t),
    (selectUnary tag fallback choices).Exec (q,S) e (t+2*g+1) := by
  induction g with
  | zero =>
    intro choices P hget S q hTag e t hbody
    cases choices with
    | nil => simp at hget
    | cons Q Qs =>
      have hQP : Q=P := by simpa using hget
      subst Q
      have he : Function.update S tag []=S := by
        funext k
        by_cases hk : k=tag <;> simp_all [unary]
      have hb := hbody none
      rw [he] at hb
      have hh := ifPeek_false tag Option.isSome (seq (pop tag) (selectUnary tag fallback Qs)) P
        (d := (q,S)) (by simp [hTag,unary]) (by simpa [hTag,unary] using hb)
      simpa only [selectUnary,Nat.mul_zero,Nat.add_zero] using hh
  | succ g ih =>
    intro choices P hget S q hTag e t hbody
    cases choices with
    | nil => simp at hget
    | cons Q Qs =>
      have hget' : Qs[g]?=some P := by simpa using hget
      let S1 := Function.update S tag (unary g)
      have hp : (pop tag).Exec (some true,S) (some true,S1) 1 := by
        simpa [hTag,unary,List.replicate_succ,S1] using pop_exec tag (some true,S)
      have ht := ih Qs P hget' S1 (some true) (by simp [S1]) e t (by
        intro q
        simpa only [S1,Function.update_idem] using hbody q)
      have hb := seq_exec _ _ hp ht
      have hh := ifPeek_true tag Option.isSome (seq (pop tag) (selectUnary tag fallback Qs)) Q
        (d := (q,S)) (by simp [hTag,unary,List.replicate_succ])
        (by simpa [hTag,unary,List.replicate_succ] using hb)
      change (selectUnary tag fallback (Q::Qs)).Exec (q,S) e _ at hh
      convert hh using 1 <;> omega

end QMAPerfectCompleteness.Uniformity.StructuredStack.Code


