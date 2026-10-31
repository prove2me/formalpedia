-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_bivariateCDF
-- name    : KallMayerSLP_Bonferroni_bivariateCDF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:06.082979+00:00
-- url     : https://prove2.me/theorems/fadca2ef-5f55-44ad-8050-e3d05db4fcae
-- title:
--   Two-dimensional marginal distribution function $F_{ij}$
-- statement:
--   The distribution function of the two-dimensional marginal distribution of $(\xi_i,\xi_j)$:
--   $$
--   F_{ij}(s,t)=\mathbb P(\xi_i\le s,\ \xi_j\le t).
--   $$
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, p.289 (PDF 298)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- The distribution function `F_ij(s, t) = ℙ(ξ_i ≤ s, ξ_j ≤ t)` of the two-dimensional marginal
distribution of `(ξ_i, ξ_j)`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, §3.4, p.289 (PDF 298). -/
noncomputable def bivariateCDF {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {r : ℕ}
    (ξ : Ω → Fin r → ℝ) (i j : Fin r) (s t : ℝ) : ℝ :=
  μ.real {ω | ξ ω i ≤ s ∧ ξ ω j ≤ t}

end KallMayerSLP.Bonferroni


