-- Prove2me | Definitions.Def_ChapterCoherentOverlapComplex
-- name    : ChapterCoherentOverlapComplex
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:46:56.632323+00:00
-- url     : https://prove2.me/theorems/65ea4e79-d747-4d60-a4f6-bd4fc0e26568
-- title:
--   Chapter CoherentOverlapComplex
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCoherentOverlapComplex.lean`): generated def bundle for ChapterCoherentOverlapComplex. See BookProof/ChapterCoherentOverlapComplex.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCoherentOverlapComplex.lean

import Definitions.Def_ChapterCoherentOverlap
import Mathlib


/-!
# Chapter "The Coherent State of Attention" — the **complex** Bargmann kernel and
the phase-invariance of the Born weight

`BookProof.ChapterCoherentOverlap` and `BookProof.ChapterSoftmaxBorn` prove the
coherent-overlap and Softmax-is-Born identities for *real* coherent-state
parameters, where the Bargmann–Fock kernel is a positive real number.  Both
modules record the same disparity with the informal chapter, which states the
kernel for general **complex** parameters:

  `⟨q | k⟩ = exp (-‖q‖²/2 - ‖k‖²/2 + ⟪q, k⟫)`,   `q, k ∈ ℂⁿ`,

where now `⟪q, k⟫ = ∑ᵢ conj (qᵢ) kᵢ` is a complex number, so the kernel carries an
extra phase `exp (i · Im ⟪q,k⟫)`.  This module closes that disparity: it defines
the complex kernel, factors it into modulus and phase, and shows that the Born
rule — the squared modulus — *discards the phase*, so the attention weights are
exactly the ones computed in the real case, with the alignment score being the
real part `Re ⟪q, k⟫` (which is what a real-valued attention logit is).

Deliverables (all `sorry`-free, `axiom`-free):

* `coherentOverlapC` — the complex Bargmann–Fock reproducing kernel;
* `coherentOverlapC_eq_sum` — the coordinate formula;
* `coherentOverlapC_eq_modulus_mul_phase` — **the modulus/phase factorization**:
  the kernel is a positive real Gaussian factor times a pure phase
  `exp (i · Im ⟪q,k⟫)`;
* `norm_coherentOverlapC` — the modulus is the real Gaussian factor;
* `coherentOverlapC_self`, `norm_coherentOverlapC_le_one` — normalization and the
  Cauchy–Schwarz bound;
* `coherentOverlapC_ofReal`, `bornNumerC_ofReal` — the real theory of
  `ChapterCoherentOverlap` is the special case of real parameters;
* `bornNumerC_eq` — **the three-factor split** of `|⟨q|k⟩|²` with `Complex.normSq`;
* `bornWeightC`, `softmaxC` and the **HEADLINE `coherentBornC_eq_softmax`** — for
  complex coherent-state parameters with a common key norm, the Born weight is
  exactly the Softmax attention weight at inverse temperature `2` in the real
  alignment scores `Re ⟪q, kⱼ⟫`;
* `bornWeightC_phase_invariant` — the Born weight is unchanged if each key is
  replaced by a key with the same norm and the same real alignment, i.e. the
  phase of the overlap is invisible to attention.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterCoherentOverlapComplex

variable {n m : ℕ}

/-! ## The complex Bargmann–Fock kernel -/

/-- The **complex coherent-state overlap** (Bargmann–Fock reproducing kernel):
`⟨q | k⟩ = exp (-‖q‖²/2 - ‖k‖²/2 + ⟪q, k⟫)` for complex parameters. -/
def coherentOverlapC (q k : EuclideanSpace ℂ (Fin n)) : ℂ :=
  Complex.exp (((-‖q‖ ^ 2 / 2 - ‖k‖ ^ 2 / 2 : ℝ) : ℂ) + inner ℂ q k)















/-! ## The real theory is the special case of real parameters -/

/-- The inclusion of real coherent-state parameters into complex ones. -/
def ofRealVec (q : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun i => (q i : ℂ)







/-! ## The Born rule on complex coherent states -/

/-- The Born numerator for complex parameters: `|⟨q|k⟩|²`. -/
def bornNumerC (q k : EuclideanSpace ℂ (Fin n)) : ℝ := ‖coherentOverlapC q k‖ ^ 2







/-- The **Born-rule attention weight** for complex coherent-state parameters. -/
def bornWeightC (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n))
    (j : Fin m) : ℝ :=
  bornNumerC q (k j) / ∑ l, bornNumerC q (k l)

/-- The **Softmax attention weight** at inverse temperature `beta` in the real
alignment scores `Re ⟪q, kⱼ⟫`. -/
def softmaxC (beta : ℝ) (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : ℝ :=
  Real.exp (beta * (inner ℂ q (k j) : ℂ).re) /
    ∑ l, Real.exp (beta * (inner ℂ q (k l) : ℂ).re)



















end BookProof.ChapterCoherentOverlapComplex

end


