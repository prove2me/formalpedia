-- Prove2me | Definitions.Def_ComplementarySourcing_Supplement_uncappedDemand
-- name    : ComplementarySourcing_Supplement_uncappedDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:41:04.673987+00:00
-- url     : https://prove2.me/theorems/8823d7e1-50d6-4144-b31a-de3335fef630
-- title:
--   Market demand without market risk, $\mu\,u(x_m,x_s)$
-- statement:
--   Without market risk (the benchmark $\epsilon\to\infty$ of §3.1) market taste never caps demand, so the demand $d(x_m,x_s,\epsilon)=\mu\min\{u(x_m,x_s),\epsilon\}$ becomes
--
--   $$\mu\,u(x_m,x_s)=\mu\,(x_m+x_s+\alpha x_m x_s),$$
--
--   where $x_m,x_s\ge0$ are the manufacturer's and the supplier's efforts, $\alpha\ge0$ the complementarity and $\mu>0$ the market size.
--
--   This is the demand of the no-risk Models (M) and (S) of Theorem 1.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.7 and §3.1, p.9

import Mathlib

namespace ComplementarySourcing

/-- Market demand without market risk, `µ u(x_m, x_s) = µ (x_m + x_s + α x_m x_s)`: the demand
`d(x_m, x_s, ϵ) = µ min{u(x_m, x_s), ϵ}` of p.7 in the benchmark `ϵ → ∞` of §3.1, where market
taste never caps demand. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), p.7 and §3.1, p.9 (PDF 7, 9).

**Formalization Note.** For `ϵ ≥ u(x_m, x_s)` this is `ComplementarySourcing.demand µ α x_m x_s ϵ`. -/
noncomputable def Supplement.uncappedDemand (μ α xm xs : ℝ) : ℝ :=
  μ * (xm + xs + α * xm * xs)

end ComplementarySourcing


