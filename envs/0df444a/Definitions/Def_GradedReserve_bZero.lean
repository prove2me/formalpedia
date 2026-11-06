-- Prove2me | Definitions.Def_GradedReserve_bZero
-- name    : GradedReserve_bZero
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:40.839769+00:00
-- url     : https://prove2.me/theorems/4ca38d93-975e-4088-85e4-bf8170ea141c
-- title:
--   $b_0=\bar v\,(p+m)/(p+\ell)$
-- statement:
--   $$b_0=\bar v\,\frac{p+m}{p+\ell}=c_0\bar v,$$
--   the bid at which the optimal graded reserve reaches acceptance probability one.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.1, p.5 (PDF 6)

import Mathlib
import Definitions.Def_GradedReserve_vbar
import Definitions.Def_GradedReserve_cZero
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `b₀ = v̄ (p + m)/(p + ℓ)` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.1, p.5, PDF 6). -/
noncomputable def bZero (k : ℝ) (n : ℕ) (p : ℝ) : ℝ := vbar k n p * cZero k n p

end GradedReserve


