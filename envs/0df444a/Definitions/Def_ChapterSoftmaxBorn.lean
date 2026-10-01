-- Prove2me | Definitions.Def_ChapterSoftmaxBorn
-- name    : ChapterSoftmaxBorn
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:42:21.007886+00:00
-- url     : https://prove2.me/theorems/63fcf79f-08b6-44ce-85a2-dd1a07f64676
-- title:
--   Chapter SoftmaxBorn
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSoftmaxBorn.lean`): generated def bundle for ChapterSoftmaxBorn. See BookProof/ChapterSoftmaxBorn.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSoftmaxBorn.lean

import Definitions.Def_ChapterCoherentOverlap
import Mathlib


/-!
# Chapter "The Coherent State of Attention", §"Softmax Is the Born Rule on
Coherent States" — the headline identity

Formalization of the headline claim of the new chapter `Book/CoherentState.lean`
(adapted from `coherent.md`): applying the **Born rule** (normalized squared
modulus) to the coherent-state overlaps of a query `q` against a family of keys
`k : Fin m → ℝⁿ` produces **exactly the Softmax attention weights** at inverse
temperature `2`, provided the keys have a common norm (LayerNorm / RMSNorm).

The mathematical content is a finite `Finset` identity.  Writing
`⟨q|k_j⟩ = exp (-‖q‖²/2 - ‖k_j‖²/2 + ⟪q,k_j⟫)` (`ChapterCoherentOverlap`), the
Born numerator splits into three factors

  `|⟨q|k_j⟩|² = exp (-‖q‖²) · exp (-‖k_j‖²) · exp (2⟪q,k_j⟫)`,

of which the first is independent of `j` and cancels between numerator and
denominator, and the second is *also* independent of `j` once the keys are
normalized, and cancels too.  What is left is Softmax.

Deliverables (all `sorry`-free, `axiom`-free):

* `bornWeight` — the Born-rule attention weight built from coherent overlaps;
* `softmax` — the usual Softmax attention weight at inverse temperature `beta`;
* `coherentBorn_sq_eq` — **the three-factor split** of `|⟨q|k⟩|²`;
* `bornWeight_nonneg`, `bornWeight_pos`, `bornWeight_sum_one` — the Born weights
  are a genuine probability distribution over the keys;
* `softmax_nonneg`, `softmax_pos`, `softmax_sum_one` — likewise for Softmax;
* `coherentBorn_cancel_q` — the `exp (-‖q‖²)` factor cancels: the Born weight is
  already independent of the query norm;
* **HEADLINE `coherentBorn_eq_softmax`** — under a constant key norm, the Born
  rule on coherent states *is* Softmax attention at inverse temperature `2`
  (equivalently temperature `τ = 1/2`);
* `coherentBorn_eq_softmax_of_unit_keys` — the LayerNorm special case `‖k_j‖ = 1`.

**Recorded disparity with the informal chapter.**  The chapter states the overlap
for general (complex) Bargmann parameters; the theorems here are proved for
*real* parameters, where the overlap is a positive real.  The complex case adds
only a phase `exp (i · Im ⟪q,k⟫)`, which the Born rule (squared modulus) discards,
so the weight formula is unchanged.  **This disparity is now closed**: the complex
case is formalized in `BookProof.ChapterCoherentOverlapComplex`
(`coherentBornC_eq_softmax`, `bornWeightC_phase_invariant`), and
`bornWeightC_ofReal` identifies the weights below as its real special case.
The chapter's informal step "each `exp(-‖k_j‖²)` is a fixed constant" is a genuine
hypothesis, and appears as the explicit assumption `∀ l, ‖k l‖ = r`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterSoftmaxBorn

open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

/-! ## The Born numerator and its three-factor split -/

/-- The Born-rule numerator: the squared modulus of the coherent-state overlap
`|⟨q | k⟩|²`. -/
def bornNumer (q k : EuclideanSpace ℝ (Fin n)) : ℝ := coherentOverlap q k ^ 2





/-! ## The Born weights and the Softmax weights -/

/-- The **Born-rule attention weight**: the normalized squared overlap of the
query coherent state with the `j`-th key coherent state. -/
def bornWeight (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n))
    (j : Fin m) : ℝ :=
  bornNumer q (k j) / ∑ l, bornNumer q (k l)

/-- The **Softmax attention weight** at inverse temperature `beta` (temperature
`τ = 1/beta`). -/
def softmax (beta : ℝ) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : ℝ :=
  Real.exp (beta * inner ℝ q (k j)) / ∑ l, Real.exp (beta * inner ℝ q (k l))

















/-! ## Cancelling the query factor -/



/-! ## The headline: Softmax is the Born rule -/







end BookProof.ChapterSoftmaxBorn

end


