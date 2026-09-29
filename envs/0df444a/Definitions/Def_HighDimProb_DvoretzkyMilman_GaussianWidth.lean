-- Prove2me | Definitions.Def_HighDimProb_DvoretzkyMilman_GaussianWidth
-- name    : HighDimProb_DvoretzkyMilman_GaussianWidth
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:12:42.774864+00:00
-- url     : https://prove2.me/theorems/04cbfa4d-c609-4f3b-b37a-c6451c9b4a2a
-- title:
--   The Gaussian width $w(T)$ of a subset of $\mathbb R^n$
-- statement:
--   The **Gaussian width** of a subset $T\subseteq\mathbb R^n$: $w(T) := \mathbb E\sup_{x\in T}
--   \langle g,x\rangle$, where $g\sim N(0,I_n)$. This is the quantity the goal theorem's ball
--   radius, and (via `StableDimension`) its measurement-count hypothesis, are stated in terms of.
--
--   **Formalization Note** The standard Gaussian vector $g\sim N(0,I_n)$ is realized as the
--   identity map on Mathlib's own standard Gaussian measure on a finite-dimensional real inner
--   product space (`ProbabilityTheory.stdGaussian`); $E\sup$ is `ExpSup`.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 173, Definition 7.5.1

import Mathlib
import Definitions.Def_HighDimProb_DvoretzkyMilman_ExpSup

open MeasureTheory ProbabilityTheory

namespace HighDimProb.DvoretzkyMilman

/-- The **Gaussian width** `w(T)` of a subset `T ⊆ ℝⁿ`. Vershynin, *High-Dimensional Probability*
(2018), Definition 7.5.1, p. 173 (PDF p. 181): "The Gaussian width of a subset `T ⊂ ℝⁿ` is defined
as `w(T) := E sup_{x∈T} ⟨g,x⟩` where `g ∼ N(0, Iₙ)`." The standard Gaussian vector `g ∼ N(0,Iₙ)` is
realized as the identity map on Mathlib's own standard Gaussian measure on a finite-dimensional
real inner product space (`ProbabilityTheory.stdGaussian`), as in `08-matrix-deviation`'s own copy
of this definition (that chunk's copy is still a draft, so per Addendum 2 rule 5 this chapter
redefines its own copy rather than importing it). `E sup` is `expSup`. -/
noncomputable def gaussianWidth {n : ℕ} (T : Set (EuclideanSpace ℝ (Fin n))) : EReal :=
  expSup (stdGaussian (EuclideanSpace ℝ (Fin n))) (fun x : T => fun g => inner (𝕜 := ℝ) g x.1)

end HighDimProb.DvoretzkyMilman


