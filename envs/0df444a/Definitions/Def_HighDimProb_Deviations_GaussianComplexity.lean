-- Prove2me | Definitions.Def_HighDimProb_Deviations_GaussianComplexity
-- name    : HighDimProb_Deviations_GaussianComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:07:27.287534+00:00
-- url     : https://prove2.me/theorems/567cac09-0404-4354-b4a2-fbf4f2dc31d0
-- title:
--   The Gaussian complexity $\gamma(T)$ of a subset of $\mathbb R^n$
-- statement:
--   The **Gaussian complexity** of a subset $T\subseteq\mathbb R^n$: $\gamma(T) :=
--   \mathbb E\sup_{x\in T}|\langle g,x\rangle|$, where $g\sim N(0,I_n)$. This is the quantity the
--   right-hand side of the goal theorem (Theorem 9.1.1) is stated in terms of.
--
--   **Formalization Note** The standard Gaussian vector $g\sim N(0,I_n)$ is realized as the
--   identity map on Mathlib's own standard Gaussian measure on a finite-dimensional real inner
--   product space (`ProbabilityTheory.stdGaussian`); $E\sup$ is `ExpSup` (this chunk's own copy of
--   the finite-marginal convention).
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 180, Definition 7.6.8

import Mathlib
import Definitions.Def_HighDimProb_Deviations_ExpSup

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Deviations

/-- The **Gaussian complexity** `γ(T)` of a subset `T ⊆ ℝⁿ`. Vershynin, *High-Dimensional
Probability* (2018), Definition 7.6.8, p. 180 (PDF p. 188): "The Gaussian complexity of a subset
`T ⊂ ℝⁿ` is defined as `γ(T) := E sup_{x∈T} |⟨g,x⟩|` where `g ∼ N(0, Iₙ)`." The standard Gaussian
vector `g ∼ N(0,Iₙ)` is realized as the identity map on `(EuclideanSpace ℝ (Fin n),
ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n)))` — Mathlib's own standard Gaussian
measure on a finite-dimensional real inner product space, "the random vector whose coordinates in
an orthonormal basis are independent standard Gaussian" (`Mathlib.Probability.Distributions.
Gaussian.Multivariate`), matching `g ∼ N(0,Iₙ)` exactly. `E sup` is `expSup` (through finite
marginals, `EReal`-valued, this chunk's own copy of the book-wide convention set in footnote 3 to
Section 7.2). -/
noncomputable def gaussianComplexity {n : ℕ} (T : Set (EuclideanSpace ℝ (Fin n))) : EReal :=
  expSup (stdGaussian (EuclideanSpace ℝ (Fin n))) (fun x : T => fun g => |inner (𝕜 := ℝ) g x.1|)

end HighDimProb.Deviations


