-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_marginalCDF
-- name    : KallMayerSLP_Bonferroni_marginalCDF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:06.088591+00:00
-- url     : https://prove2.me/theorems/a9653fa2-38fa-48c5-b384-7833e78536c2
-- title:
--   One-dimensional marginal distribution function $F_i$
-- statement:
--   The distribution function of the $i$-th one dimensional marginal distribution of $\xi$:
--   $$
--   F_i(t)=\mathbb P(\xi_i\le t).
--   $$
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, p.289 (PDF 298)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- The distribution function `F_i(t) = ℙ(ξ_i ≤ t)` of the `i`-th one dimensional marginal
distribution of `ξ`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, §3.4, p.289 (PDF 298). -/
noncomputable def marginalCDF {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {r : ℕ}
    (ξ : Ω → Fin r → ℝ) (i : Fin r) (t : ℝ) : ℝ :=
  μ.real {ω | ξ ω i ≤ t}

end KallMayerSLP.Bonferroni


