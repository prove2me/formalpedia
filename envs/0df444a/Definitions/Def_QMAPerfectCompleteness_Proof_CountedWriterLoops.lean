-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CountedWriterLoops
-- name    : QMAPerfectCompleteness_Proof_CountedWriterLoops
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:03:49.135986+00:00
-- url     : https://prove2.me/theorems/9e87d3ea-7ae9-4bfb-b6df-a8e12eeaa0c2
-- title:
--   Counted unary loops with accumulated output
-- statement:
--   Defines finite increasing and decreasing loops over unary counters. The execution specifications record the order of emitted words, accumulated body-time bounds and preservation of unrelated stacks.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CountedWriterLoops.lean, retained declaration span lines 11–120.

/- Generated from Solutions.CountedWriterLoops by authoritative Stage-2 skeleton subtraction.
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



/-! Literal finite counted loops for circuit-code writers, with exact accumulated output and
runtime bounds. Counter registers are unary and all unrelated stacks are preserved. -/
open Turing StateTransition
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Uniformity.StructuredStack.Code
variable {K : Type} [DecidableEq K]

abbrev countUpBody (remaining index : K) (P : Code K) : Code K :=
  seq (pop remaining) (seq P (push index true))
abbrev countUp (remaining index : K) (P : Code K) : Code K :=
  whilePeek remaining Option.isSome (countUpBody remaining index P)

def loopStore (S : K → List Bool) (remaining index output : K)
    (r j : ℕ) (bits : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update S remaining (unary r)) index (unary j)) output bits

def upWords (F : ℕ → List Bool) (j : ℕ) : ℕ → List Bool
  | 0 => []
  | n+1 => F j ++ upWords F (j+1) n

/-- A finite ascending loop consumes its remaining-count register and appends precisely the
successive body outputs; its time is linear in the number of iterations and the body bound. -/
theorem countUp_exec (remaining index output : K)
    (hri : remaining ≠ index) (hro : remaining ≠ output) (hio : index ≠ output)
    (P : Code K) (S : K → List Bool) (F : ℕ → List Bool) (T limit : ℕ)
    (hbody : ∀ j r bits q, j<limit →
      P.Exec (q,loopStore S remaining index output r j bits)
        (none,loopStore S remaining index output r j ((F j).reverse++bits)) T)
    (n j : ℕ) (bits : List Bool) (q : Option Bool) (hlimit : j+n≤limit) :
    (countUp remaining index P).Exec
      (q,loopStore S remaining index output n j bits)
      (none,loopStore S remaining index output 0 (j+n) ((upWords F j n).reverse++bits))
      (n*(T+3)+1) := by
  induction n generalizing j bits q with
  | zero =>
    have hh := while_false remaining Option.isSome (countUpBody remaining index P)
      (q,loopStore S remaining index output 0 j bits)
      (by simp [loopStore,hri,hro])
    simpa [loopStore,hri,hro,upWords] using hh
  | succ n ih =>
    let S₀ := loopStore S remaining index output (n+1) j bits
    let S₁ := loopStore S remaining index output n j bits
    let S₂ := loopStore S remaining index output n j ((F j).reverse++bits)
    let S₃ := loopStore S remaining index output n (j+1) ((F j).reverse++bits)
    have hp := pop_exec remaining (some true,S₀)
    have hs₁ : Function.update S₀ remaining (S₀ remaining).tail=S₁ := by
      funext k
      by_cases hr : k=remaining <;> by_cases hi : k=index <;> by_cases ho : k=output <;>
        simp_all [S₀,S₁,loopStore,unary,List.replicate_succ]
    rw [hs₁] at hp
    have hhead : (S₀ remaining).head?=some true := by simp [S₀,loopStore,hri,hro,unary,List.replicate_succ]
    have hp' : (pop remaining).Exec (some true,S₀) (some true,S₁) 1 := by
      simpa only [hhead] using hp
    have hb := hbody j n bits (some true) (by omega)
    have hpush := push_exec index true (none,S₂)
    have hs₃ : Function.update S₂ index (true::S₂ index)=S₃ := by
      funext k
      by_cases hr : k=remaining <;> by_cases hi : k=index <;> by_cases ho : k=output <;>
        simp_all [S₂,S₃,loopStore,unary,List.replicate_succ]
    rw [hs₃] at hpush
    have hblock := seq_exec _ _ hp' (seq_exec _ _ hb hpush)
    have ht := ih (j+1) ((F j).reverse++bits) none (by omega)
    have hh := while_true remaining Option.isSome (countUpBody remaining index P)
      (d := (q,S₀)) (by simp [S₀,loopStore,hri,hro,unary,List.replicate_succ])
      (by simpa only [hhead] using hblock) ht
    have hidx : j+1+n=j+(n+1) := by omega
    have hbits : (upWords F (j+1) n).reverse++((F j).reverse++bits) =
        (upWords F j (n+1)).reverse++bits := by simp [upWords,List.reverse_append,List.append_assoc]
    rw [hidx,hbits] at hh
    convert hh using 1 <;> ring

abbrev countDown (index : K) (P : Code K) : Code K :=
  whilePeek index Option.isSome (seq (pop index) P)

def downStore (S : K → List Bool) (index output : K) (j : ℕ) (bits : List Bool) : K → List Bool :=
  Function.update (Function.update S index (unary j)) output bits

def downWords (F : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | n+1 => F n++downWords F n

/-- A descending loop consumes its index and emits the body at n−1,n−2,…,0. -/
theorem countDown_exec (index output : K) (hio : index ≠ output)
    (P : Code K) (S : K → List Bool) (F : ℕ → List Bool) (T limit : ℕ)
    (hbody : ∀ j bits q, j<limit →
      P.Exec (q,downStore S index output j bits)
        (none,downStore S index output j ((F j).reverse++bits)) T)
    (n : ℕ) (bits : List Bool) (q : Option Bool) (hn : n≤limit) :
    (countDown index P).Exec (q,downStore S index output n bits)
      (none,downStore S index output 0 ((downWords F n).reverse++bits)) (n*(T+2)+1) := by
  induction n generalizing bits q with
  | zero =>
    have hh := while_false index Option.isSome (seq (pop index) P)
      (q,downStore S index output 0 bits) (by simp [downStore,hio])
    simpa [downStore,hio,downWords] using hh
  | succ n ih =>
    let S₀ := downStore S index output (n+1) bits
    let S₁ := downStore S index output n bits
    have hp := pop_exec index (some true,S₀)
    have hs₁ : Function.update S₀ index (S₀ index).tail=S₁ := by
      funext k
      by_cases hi : k=index <;> by_cases ho : k=output <;>
        simp_all [S₀,S₁,downStore,unary,List.replicate_succ]
    rw [hs₁] at hp
    have hhead : (S₀ index).head?=some true := by simp [S₀,downStore,hio,unary,List.replicate_succ]
    have hp' : (pop index).Exec (some true,S₀) (some true,S₁) 1 := by
      simpa only [hhead] using hp
    have hb := hbody n bits (some true) (by omega)
    have hblock := seq_exec _ _ hp' hb
    have ht := ih ((F n).reverse++bits) none (by omega)
    have hh := while_true index Option.isSome (seq (pop index) P)
      (d := (q,S₀)) (by simp [S₀,downStore,hio,unary,List.replicate_succ])
      (by simpa only [hhead] using hblock) ht
    have hbits : (downWords F n).reverse++((F n).reverse++bits) =
        (downWords F (n+1)).reverse++bits := by simp [downWords,List.reverse_append,List.append_assoc]
    rw [hbits] at hh
    convert hh using 1 <;> ring

end QMAPerfectCompleteness.Uniformity.StructuredStack.Code


