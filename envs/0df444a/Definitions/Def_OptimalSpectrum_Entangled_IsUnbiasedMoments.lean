-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_IsUnbiasedMoments
-- name    : OptimalSpectrum_Entangled_IsUnbiasedMoments
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:37.627931+00:00
-- url     : https://prove2.me/theorems/b7af56eb-adab-4be8-98e8-6615e7117881
-- title:
--   Unbiased moment estimates with finite variances
-- statement:
--   Real random variables $\widehat M_1,\dots,\widehat M_K$ on a probability space are **unbiased moment estimates with finite variances** for a spectrum $\alpha\in\mathbb R^d$ when, for every $1\le m\le K$,
--
--   $$\mathbb E\,\widehat M_m^2<\infty\qquad\text{and}\qquad \mathbb E\,\widehat M_m=\sum_{i=1}^d\alpha_i^m .$$
--
--   No independence between the estimates is assumed, as on the page.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §6 Setup, p. 13 (PDF p. 15)

import Mathlib

open MeasureTheory

namespace OptimalSpectrum.Entangled

/-- **Unbiased moment estimates with finite variances.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §6 Setup, printed p. 13 (PDF p. 15): "Let M̂₁, …, M̂_K be unbiased real estimates of the
monomial moments ∑_i α_i^m, with finite variances … No independence assumption on the moment
estimates is needed."

For `1 ≤ m ≤ K`, `M̂_m` is square integrable (`MemLp 2`, which includes measurability) and
`E M̂_m = ∑ᵢ αᵢ^m`. No joint condition is imposed. -/
def IsUnbiasedMoments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {d : ℕ} (K : ℕ)
    (Mhat : ℕ → Ω → ℝ) (α : Fin d → ℝ) : Prop :=
  ∀ m, 1 ≤ m → m ≤ K → MemLp (Mhat m) 2 μ ∧ ∫ ω, Mhat m ω ∂μ = ∑ i, α i ^ m

end OptimalSpectrum.Entangled


