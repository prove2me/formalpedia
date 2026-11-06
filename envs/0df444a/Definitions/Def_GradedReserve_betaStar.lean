-- Prove2me | Definitions.Def_GradedReserve_betaStar
-- name    : GradedReserve_betaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:37.720131+00:00
-- url     : https://prove2.me/theorems/c9939fb6-d66e-40fc-afb1-8cbfd5521a75
-- title:
--   Equilibrium bid $\beta^*$ of display (30)
-- statement:
--   The equilibrium bid of the optimal graded-reserve auction,
--   $$\beta^*(v)=\begin{cases}\dfrac{p+m}{p+\ell}\,v, & 0\le v\le\bar v,\\[2mm] \dfrac m\ell\,v+\dfrac{p\,\bar v^{\,\ell}}{\ell(p+\ell)\,v^m}, & \bar v\le v\le1.\end{cases}$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.1 part 2, p.5 (PDF 6); display (30), p.19 (PDF 20)

import Mathlib
import Definitions.Def_GradedReserve_powM
import Definitions.Def_GradedReserve_powL
import Definitions.Def_GradedReserve_vbar
import Definitions.Def_GradedReserve_cZero
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The equilibrium bid (30) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.1 part 2, p.5, PDF 6; display (30), p.19, PDF 20):
`β*(v) = (p+m)/(p+ℓ) v` for `v ≤ v̄` and `β*(v) = (m/ℓ) v + p v̄^ℓ/(ℓ(p+ℓ) v^m)` for `v ≥ v̄`. -/
noncomputable def betaStar (k : ℝ) (n : ℕ) (p v : ℝ) : ℝ :=
  if v ≤ vbar k n p then cZero k n p * v
  else powM k n / powL k n * v
    + p * vbar k n p ^ powL k n / (powL k n * (p + powL k n) * v ^ powM k n)

end GradedReserve


