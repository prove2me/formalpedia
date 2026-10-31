-- Prove2me | Definitions.Def_ComplementarySourcing_demand
-- name    : ComplementarySourcing_demand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:34.084671+00:00
-- url     : https://prove2.me/theorems/cc94aab6-d8d0-47a6-9a14-411e3b6f5aad
-- title:
--   Market demand
-- statement:
--   For efforts $x_m,x_s$ and market taste $\epsilon$, demand is
--
--   $$d(x_m,x_s,\epsilon)=\mu\min\{x_m+x_s+\alpha x_mx_s,\ \epsilon\}.$$
--
--   The first argument of the minimum is the user experience $u(x_m,x_s)$; the market taste caps what the product's performance can sell.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.7

import Mathlib

namespace ComplementarySourcing

/-- Market demand `d(x_m, x_s, ϵ) = µ min{x_m + x_s + α x_m x_s, ϵ}`, Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), p.7 (PDF 7).
The first argument of the minimum is the user experience `u(x_m, x_s)`. -/
noncomputable def demand (μ α xm xs ε : ℝ) : ℝ :=
  μ * min (xm + xs + α * xm * xs) ε

end ComplementarySourcing


