-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_jointCDF
-- name    : KallMayerSLP_Bonferroni_jointCDF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:04.841018+00:00
-- url     : https://prove2.me/theorems/349c371c-975b-449c-b1c5-baee6a7662f2
-- title:
--   Distribution function $F$ of a random vector
-- statement:
--   The probability distribution function of the random vector $\xi:\Omega\to\mathbb R^r$ is
--   $$
--   F(x)=\mathbb P(\xi_1\le x_1,\dots,\xi_r\le x_r),\qquad x\in\mathbb R^r.
--   $$
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, pp.284–285 (PDF 293–294), eq. (3.8)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- The probability distribution function `F(x) = ℙ(ξ₁ ≤ x₁, …, ξ_r ≤ x_r)` of a random vector
`ξ : Ω → ℝ^r`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, §3.4, pp.284–285 (PDF 293–294), left-hand side of (3.8). -/
noncomputable def jointCDF {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {r : ℕ}
    (ξ : Ω → Fin r → ℝ) (x : Fin r → ℝ) : ℝ :=
  μ.real {ω | ∀ i, ξ ω i ≤ x i}

end KallMayerSLP.Bonferroni


