-- Prove2me | Definitions.Def_ComplementarySourcing_Supplement_recourseRevenue
-- name    : ComplementarySourcing_Supplement_recourseRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:46:05.360745+00:00
-- url     : https://prove2.me/theorems/5da76d7f-9c66-5d32-bf19-db9ef3c52f59
-- title:
--   A firm's revenue at the optimal recourse selling price
-- statement:
--   With endogenous selling price (§4.3), demand at selling price $r$ is linear, $D(r\mid x_m,x_s,\epsilon)=d-br$ with $d=d(x_m,x_s,\epsilon)$ and slope $b>0$. After observing the market taste the manufacturer sets the selling price
--
--   $$r^*(d)=\frac{d}{2b},$$
--
--   and a firm whose unit margin is the fraction $\theta$ of the selling price (the supplier $\theta=\eta$, the manufacturer $\theta=1-\eta$) earns $\theta\,r^*(d)\,\big(d-b\,r^*(d)\big)$, which equals $\theta d^2/(4b)$.
--
--   It gives both firms' payoffs in the models of Theorem 5.
--
--   **Formalization Note** The recourse price is substituted at its optimum $d/(2b)$, the unique maximizer of $(1-\eta)\,r\,(d-br)$ for $b>0$, $\eta<1$.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), §4.3, p.23; §A6, p.A23

import Mathlib

namespace ComplementarySourcing

/-- A firm's revenue at the optimal recourse selling price (§4.3, §A6). With linear demand
`D(r | x_m, x_s, ϵ) = d − b r`, where `d = d(x_m, x_s, ϵ)`, the manufacturer sets
`r*(d) = d / (2b)`, and a firm whose unit margin is the fraction `θ` of the selling price (the
supplier `θ = η`, the manufacturer `θ = 1 − η`) earns `θ r* (d − b r*)`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), §4.3, p.23 (PDF 23), and §A6, p.A23 (PDF 51).

**Formalization Note.** The recourse price is substituted at its optimum `d / (2b)`, the
unique maximizer of `(1 − η) r (d − b r)` for `b > 0` and `η < 1` (the page: the price "does not
depend on the relative power η"). -/
noncomputable def Supplement.recourseRevenue (b θ d : ℝ) : ℝ :=
  θ * (d / (2 * b)) * (d - b * (d / (2 * b)))

end ComplementarySourcing


