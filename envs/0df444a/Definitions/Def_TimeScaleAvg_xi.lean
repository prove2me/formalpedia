-- Prove2me | Definitions.Def_TimeScaleAvg_xi
-- name    : TimeScaleAvg_xi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:54.668488+00:00
-- url     : https://prove2.me/theorems/694992ae-e23a-4620-bee7-bb422452fd3b
-- title:
--   The perturbation $\xi(s)$
-- statement:
--   For $x_1\in\mathcal H$, the perturbation is
--
--   $$
--   \xi(s)=-\frac{s_0^{\alpha}}{(\alpha-1)s^{\alpha-1}}\,x_1,
--   $$
--
--   which is small for large $s$ and separates $x(s)$ from the $\mu_s$-average of $y$.
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, p.7

import Mathlib

namespace TimeScaleAvg

/-- The perturbation `ξ(s) := -(s₀^α/((α-1) s^{α-1})) x₁` of (39)
(Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.7), with `x₁ = ẋ(s₀)` passed as an argument. -/
noncomputable def xi {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (α s₀ : ℝ) (x₁ : H) (s : ℝ) : H :=
  -((s₀ ^ α / ((α - 1) * s ^ (α - 1))) • x₁)

end TimeScaleAvg


