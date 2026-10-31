-- Prove2me | Definitions.Def_ComplementarySourcing_manufacturerStageProfit
-- name    : ComplementarySourcing_manufacturerStageProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:30.592004+00:00
-- url     : https://prove2.me/theorems/3a5c0dfe-5e68-4cd6-a011-4dd6f6332ff7
-- title:
--   The manufacturer's second-stage profit in Model (S)
-- statement:
--   For given $x_s$, $w$ and realized $\epsilon$, the manufacturer as second mover maximizes
--
--   $$(r-w)\,d(x_m,x_s,\epsilon)-\tfrac12x_m^2$$
--
--   over $x_m\ge0$. Its unit margin is $r-w$.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), pp.7, 14

import Mathlib
import Definitions.Def_ComplementarySourcing_demand

namespace ComplementarySourcing

/-- The manufacturer's objective as second mover in Model (S), `(r − w) d(x_m, x_s, ϵ) − ½ x_m²`,
for given `x_s`, `w` and realized `ϵ`. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), p.14 (PDF 14); the unit margin
`r − w` is from p.7 (PDF 7). -/
noncomputable def manufacturerStageProfit (μ α r xs w ε xm : ℝ) : ℝ :=
  (r - w) * demand μ α xm xs ε - 1 / 2 * xm ^ 2

end ComplementarySourcing


