-- Prove2me | Definitions.Def_GeomDRSub_Supplement_betaStar
-- name    : GeomDRSub_Supplement_betaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:51:59.367427+00:00
-- url     : https://prove2.me/theorems/b355ccbb-9e43-426a-a802-dd0fde1ac9b8
-- title:
--   The constant $\beta^*\approx0.470439$
-- statement:
--   With $\chi=1-e^{-1/2}$, $q_0=\sqrt{(3\chi-1)/(2\chi)}$ and $\tau=2q_0(1-q_0)$,
--   $$\beta^*=\frac{4\tau}{1+6\tau+\tau^2}\approx0.470439$$
--   (Eqs. (165)–(166)). By Corollary 6.5, $U(0)=\beta^*$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 6.2, p.41, Eqs. (165)–(166)

import Mathlib

namespace GeomDRSub.Supplement

/-- **The constant `β*`**, Eqs. (165)–(166). Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Section 6.2, p.41:
`χ = 1 − e^{−1/2}`, `q₀ = √((3χ − 1)/(2χ))`, `τ = 2q₀(1 − q₀)`, `β* := 4τ/(1 + 6τ + τ²)`
(numerically `≈ 0.470439`). -/
noncomputable def betaStar : ℝ :=
  let χ : ℝ := 1 - Real.exp (-(1 / 2))
  let q₀ : ℝ := Real.sqrt ((3 * χ - 1) / (2 * χ))
  let τ : ℝ := 2 * q₀ * (1 - q₀)
  4 * τ / (1 + 6 * τ + τ ^ 2)

end GeomDRSub.Supplement


