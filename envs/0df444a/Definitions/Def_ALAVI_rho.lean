-- Prove2me | Definitions.Def_ALAVI_rho
-- name    : ALAVI_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:37.834919+00:00
-- url     : https://prove2.me/theorems/f6774e4b-e6b0-4091-8ef1-10641efddf85
-- title:
--   The constant $\rho$ of Lemma 4.1
-- statement:
--   $$
--   \rho=\min\Big\{\frac{\eta}{2\alpha(1-\eta)^2},\ \frac\tau2,\ \frac{1-\tau\gamma}{2\gamma},\ \frac1\gamma\Big\}.
--   $$
--
--   It is positive in the parameter window of Lemma 4.1.
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, Lemma 4.1, p.13

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj

namespace ALAVI

/-- **The constant ρ of Lemma 4.1**,
`ρ = min{η/(2α(1 - η)²), τ/2, (1 - τγ)/(2γ), 1/γ}`.

Zhao, Zhu & Zhang, arXiv:2306.01214v1, Lemma 4.1, p.13. -/
noncomputable def rho (η α γ τ : ℝ) : ℝ :=
  min (min (min (η / (2 * α * (1 - η) ^ 2)) (τ / 2)) ((1 - τ * γ) / (2 * γ))) (1 / γ)

end ALAVI


