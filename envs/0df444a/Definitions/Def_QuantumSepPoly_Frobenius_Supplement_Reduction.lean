-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Reduction
-- name    : QuantumSepPoly_Frobenius_Supplement_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:51:34.192119+00:00
-- url     : https://prove2.me/theorems/ae1b07bb-673d-43c9-99d1-abd624aa88e0
-- title:
--   Complete reduction behavior, fallback and tensor grouping
-- statement:
--   The operational denotation runs the constructor, takes the small-input exhaustive-search branch when $4k>n+m+2$, otherwise enforces the total sampler budget and tests both $\widehat\omega\succeq0$ and $\operatorname{Tr}(M\widehat\omega)\ge1-\varepsilon$. Success returns the $t$-fold tensor power, grouping each copy's first block into the first party and its last block into the second. Its dimension is $((N|\Omega|)^k)^t=(N|\Omega|)^{kt}$.
--
--   Failure returns a pure maximally entangled state in fixed dimension $\lfloor1/(1-\eta)\rfloor+2$; a satisfiable small input returns a fixed product state. Equality of output laws specifies implementation by a finite RAM program without installing satisfiability, PSD, a PCP, sampling, or separability as a machine instruction. Lemma 6.5 must establish the implementing code and its all-input bound; this definition supplies no such witness.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Section 6, p. 28–29, 31, 35 (PDF p. 28–29, 31, 35); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Sampling
import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_TraceGeometry

noncomputable section
open scoped BigOperators ENNReal ComplexOrder

namespace QuantumSepPoly.Frobenius.Supplement
/-- Fixed entangled failure state; its dimension exceeds 1/(1-η). -/
def fallback (η : ℝ) : Σ d, Bip d :=
  let d := Nat.floor (1/(1-η)) + 2
  ⟨d, pure (fun i : Fin d × Fin d =>
    if i.1 = i.2 then 1/(Real.sqrt d : ℂ) else 0)⟩

def separateOutput : Σ d, Bip d := ⟨1, productDensity (firstVector 1) (firstVector 1)⟩

/-- Each party groups its k registers from all t copies. -/
def groupEquiv (N A k t : ℕ) : (Fin t → Block N A k) ≃ Fin (((N*A)^k)^t) :=
  (Equiv.piCongrRight (fun _ => blockEquiv N A k)).trans (tupleEquiv ((N*A)^k) t)

def tensorOutput {N A k : ℕ} (ω : TwoBlockOp N A k) (t : ℕ) :
    Bip (((N*A)^k)^t) := fun i j =>
  ∏ l, ω ((groupEquiv N A k t).symm i.1 l, (groupEquiv N A k t).symm i.2 l)
    ((groupEquiv N A k t).symm j.1 l, (groupEquiv N A k t).symm j.2 l)

/-- Denotation of §6.2, including exhaustive search on the finite assignment
space, a global sampling cutoff, both matrix checks and the failure state.
Programs implementing this denotation are constructed by Lemma 6.5; the
mathematical PSD predicate here is never a machine instruction. -/
def reductionOutcome {n m : ℕ} (P Sample : RAMProgram) (A : ℕ) (hA : 0 < A)
    (η : ℝ) (t : ℕ) (ε : ℚ) (p : ℝ) (f : CNF3 n m) (r : RandomTape) : Σ d, Bip d := by
  classical
  let s₀ := ramResult P (cnfInput f) (splitTape r 0)
  match decodeCSP A s₀ with
  | none => exact fallback η
  | some ⟨N,I⟩ =>
    let k := registerCount N A ε
    if 4*k > n+m+2 then
      exact if Satisfiable f then separateOutput else fallback η
    else
      let s := sampleCount N A k ε
      let rr := splitTape r 1
      if totalSamplingCost (N := N) Sample s₀ k s rr > ENNReal.ofReal (samplerBudget N A k s p) then
        exact fallback η
      else
        let ω := smooth ε (empiricalState (N := N) hA Sample s₀ k s rr)
        exact if ω.PosSemidef ∧ 1-(ε : ℝ) ≤ (acceptance I k * ω).trace.re
          then ⟨((N*A)^k)^t, tensorOutput ω t⟩ else fallback η

/-- Equality of actual output laws with the operational construction. This
specifies behavior without assuming density, completeness or soundness. The
single-tape RAM may schedule independent draws in any order. -/
def ImplementsReduction (R P Sample : RAMProgram) (A : ℕ) (hA : 0 < A)
    (η : ℝ) (t : ℕ) (ε : ℚ) (C : ℝ) (e : ℕ) : Prop :=
  ∀ n m (f : CNF3 n m) (E : Set (Σ d, Bip d)),
    tapeLaw {r | (⟨(ramResult R (cnfInput f) r).nat 0,
      matrixOutput (ramResult R (cnfInput f) r)⟩ : Σ d, Bip d) ∈ E} =
    tapeLaw {r | reductionOutcome P Sample A hA η t ε (polyBound C e n m) f r ∈ E}
end QuantumSepPoly.Frobenius.Supplement


