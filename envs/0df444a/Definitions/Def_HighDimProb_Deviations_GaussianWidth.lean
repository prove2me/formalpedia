-- Prove2me | Definitions.Def_HighDimProb_Deviations_GaussianWidth
-- name    : HighDimProb_Deviations_GaussianWidth
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:07:52.458159+00:00
-- url     : https://prove2.me/theorems/b0269110-49c6-40c7-bf55-69869dd006a1
-- title:
--   The Gaussian width $w(T)$ of a subset of $\mathbb R^n$
-- statement:
--   The **Gaussian width** of a subset $T\subseteq\mathbb R^n$: $w(T) := \mathbb E\sup_{x\in T}
--   \langle g,x\rangle$, where $g\sim N(0,I_n)$ — the Gaussian complexity's "cousin" without the
--   absolute value. This is the quantity the right-hand side of the $M^*$ bound (Theorem 9.4.2) is
--   stated in terms of.
--
--   **Formalization Note** Same realization of $g\sim N(0,I_n)$ and of $E\sup$ as
--   `GaussianComplexity`, without the absolute value inside the supremum.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 173, Definition 7.5.1

import Mathlib
import Definitions.Def_HighDimProb_Deviations_ExpSup

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Deviations

/-- The **Gaussian width** `w(T)` of a subset `T ⊆ ℝⁿ`. Vershynin, *High-Dimensional Probability*
(2018), Definition 7.5.1, p. 173 (PDF p. 181): "The Gaussian width of a subset `T ⊂ ℝⁿ` is defined
as `w(T) := E sup_{x∈T} ⟨g,x⟩` where `g ∼ N(0, Iₙ)`." Same realization of `g ∼ N(0,Iₙ)` as
`gaussianComplexity` (Mathlib's `ProbabilityTheory.stdGaussian` on `EuclideanSpace ℝ (Fin n)`, via
its identity map); `E sup` is `expSup`. Unlike `gaussianComplexity`, no absolute value is taken
inside the supremum, matching the book's own distinction between the two "cousin" quantities
(Section 7.6.2: `w(T) ≤ γ(T)`, with equality when `T` is origin-symmetric). -/
noncomputable def gaussianWidth {n : ℕ} (T : Set (EuclideanSpace ℝ (Fin n))) : EReal :=
  expSup (stdGaussian (EuclideanSpace ℝ (Fin n))) (fun x : T => fun g => inner (𝕜 := ℝ) g x.1)

end HighDimProb.Deviations


