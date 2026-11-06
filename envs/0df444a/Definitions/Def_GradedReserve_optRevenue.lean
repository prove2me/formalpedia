-- Prove2me | Definitions.Def_GradedReserve_optRevenue
-- name    : GradedReserve_optRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:32.611282+00:00
-- url     : https://prove2.me/theorems/9cce74a1-643d-40aa-b909-044b288fe8ea
-- title:
--   Optimal regular-auction revenue $R^*=R_n(r^*)$
-- statement:
--   $R^*=R_n(r^*)$, the revenue of the optimal standard auction (reserve $r^*$). For $\varepsilon\in(0,1)$ the **rational revenue guarantee** is $\tau=(1-\varepsilon)R^*$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, p.4 (PDF 5)

import Mathlib
import Definitions.Def_GradedReserve_revCurve
import Definitions.Def_GradedReserve_rStar
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `R* = R_n(r*)` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, p.4, PDF 5), the optimal regular-auction revenue. The guarantee
level is `τ = (1 − ε) R*`. -/
noncomputable def optRevenue (f : ℝ → ℝ) (n : ℕ) : ℝ := revCurve f n (rStar f)

end GradedReserve


