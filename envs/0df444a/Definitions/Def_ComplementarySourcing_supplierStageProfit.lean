-- Prove2me | Definitions.Def_ComplementarySourcing_supplierStageProfit
-- name    : ComplementarySourcing_supplierStageProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:32.351396+00:00
-- url     : https://prove2.me/theorems/67b5be06-ea8b-4ff2-96f2-c7103399309c
-- title:
--   The supplier's second-stage profit in Model (M)
-- statement:
--   For given $x_m$, $w$ and realized $\epsilon$, the supplier's objective in problem (2) is
--
--   $$\pi_s(x_s\mid x_m,w,\epsilon)=w\,d(x_m,x_s,\epsilon)-\tfrac12x_s^2.$$
--
--   The supplier's production cost is normalized to zero, so $w$ is its net unit profit.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.8, eq. (2)

import Mathlib
import Definitions.Def_ComplementarySourcing_demand

namespace ComplementarySourcing

/-- The supplier's objective in problem (2), `w d(x_m, x_s, ϵ) − ½ x_s²`, for given `x_m`, `w` and
realized `ϵ`. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), eq. (2), p.8 (PDF 8). -/
noncomputable def supplierStageProfit (μ α xm w ε xs : ℝ) : ℝ :=
  w * demand μ α xm xs ε - 1 / 2 * xs ^ 2

end ComplementarySourcing


