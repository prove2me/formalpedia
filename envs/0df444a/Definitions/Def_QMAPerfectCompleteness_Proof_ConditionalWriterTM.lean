-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_ConditionalWriterTM
-- name    : QMAPerfectCompleteness_Proof_ConditionalWriterTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:09:36.573206+00:00
-- url     : https://prove2.me/theorems/f2f15ad3-e89b-4f1c-99b8-c76f3316b66c
-- title:
--   Conditional finite circuit writers
-- statement:
--   Constructs a finite writer that evaluates a unary predicate and selects one of two writer programs. The predicate workspace is cleared before the selected branch, and polynomial bounds account for evaluation and branch execution.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ConditionalWriterTM.lean, retained declaration span lines 11–72.

/- Generated from Solutions.ConditionalWriterTM by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BoundedWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CountedWriterLoops
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_StackEmbedding
import Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
import Definitions.Def_QMAPerfectCompleteness_Proof_StreamWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryEvaluator
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Compile finite generator branches using an actual unary predicate evaluator and stack test. -/
open Turing StateTransition
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Uniformity.StructuredStack.Writer
open Code
variable {I X A : Type} [DecidableEq I] [DecidableEq A]
variable {encode : X → I → List Bool} {valid : X → ℕ → Prop}

noncomputable def ifNonzero {n : (A → ℕ) → ℕ} (E : Evaluator A n)
    (read : A ↪ I) (values : X → A → ℕ)
    (hread : ∀ x a,encode x (read a)=unary (values x a))
    (hvalues : ∀ x B,valid x B → ∀ a,values x a≤B)
    {f g : X → List Bool} (Y : Writer I X encode valid f) (N : Writer I X encode valid g) :
    Writer I X encode valid (fun x=>if n (values x)=0 then g x else f x) := by
  let total := E.slots+Y.slots+N.slots
  let ew := Evaluator.block E.slots 0 total (by omega)
  let ei := evalEmb read ew
  let yi := Evaluator.block Y.slots E.slots total (by omega)
  let ni := Evaluator.block N.slots (E.slots+Y.slots) total (by omega)
  let c : WriterStacks I total := .inr (.inr (ew E.result))
  let ycode := Code.seq (Code.clear c) (Y.code.embed (frameEmb yi))
  let ncode := Code.seq (Code.clear c) (N.code.embed (frameEmb ni))
  let program := Code.seq (E.code.embed ei) (Code.ifPeek c Option.isSome ycode ncode)
  refine { slots := total, code := program, time := Polynomial.C (E.cost+2*E.growth)*(Polynomial.X+1)+Y.time+N.time+2, size := Y.size+N.size, length_bound := ?_, run := ?_ }
  · intro x B hx
    have hy := Y.length_bound x B hx
    have hn := N.length_bound x B hx
    simp only [Polynomial.eval_add]
    split_ifs <;> omega
  · intro x B hx S q hin hw
    let bound := n (values x)
    have he₀ := E.run (values x) B (hvalues x B hx) (S ∘ ei) q
      (by intro a; simpa [ei,evalEmb,hread] using hin (read a)) (by intro w; exact hw _)
    have he := Code.embed_exec_update ei E.code S q none (.inr E.result) (unary bound) _ he₀
    have hpos : ei (.inr E.result)=c := by rfl
    rw [hpos] at he
    let S₀ := Function.update S c (unary bound)
    have hc := Code.clear_exec c (unary bound) S₀ (unary bound).head? (by simp [S₀])
    have hs : Function.update S₀ c []=S := by
      funext k
      by_cases hk : k=c <;> simp_all [S₀,c,hw]
    rw [hs] at hc
    simp only [unary,List.length_replicate] at hc
    have hy := Y.runIn yi x B hx S none hin (fun w=>hw _)
    have hn := N.runIn ni x B hx S none hin (fun w=>hw _)
    have hyb := Code.seq_exec _ _ hc hy
    have hnb := Code.seq_exec _ _ hc hn
    have hbound := E.bound (values x) B (hvalues x B hx)
    by_cases hz : bound=0
    · have hguard : Option.isSome (S₀ c).head?=false := by simp [S₀,hz]
      have hb := Code.ifPeek_false c Option.isSome ycode ncode (d := (none,S₀)) hguard
        (by simpa only [S₀,Function.update_self] using hnb)
      have hh := Code.seq_exec _ _ he hb
      have hzx : n (values x)=0 := hz
      apply Code.exec_mono _ (by simpa only [hzx,ite_true] using hh)
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
      dsimp [bound] at *
      nlinarith
    · have hguard : Option.isSome (S₀ c).head?=true := by
        cases hb : bound with
        | zero => exact False.elim (hz hb)
        | succ j => simp [S₀,hb,unary,List.replicate_succ]
      have hb := Code.ifPeek_true c Option.isSome ycode ncode (d := (none,S₀)) hguard
        (by simpa only [S₀,Function.update_self] using hyb)
      have hh := Code.seq_exec _ _ he hb
      have hzx : n (values x) ≠ 0 := hz
      apply Code.exec_mono _ (by simpa only [hzx,ite_false] using hh)
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
      dsimp [bound] at *
      nlinarith

end QMAPerfectCompleteness.Uniformity.StructuredStack.Writer


