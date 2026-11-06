-- Prove2me | Definitions.Def_GradedReserve_sStar
-- name    : GradedReserve_sStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:55.683671+00:00
-- url     : https://prove2.me/theorems/5614a1a2-a937-446e-b989-1aec0d556d9e
-- title:
--   Equilibrium probability of sale $s^*(v)=\min\{(v/\bar v)^p,1\}$
-- statement:
--   $$s^*(v)=\min\{(v/\bar v)^p,\,1\},\qquad v\in[0,1].$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.1, p.5 (PDF 6)

import Mathlib
import Definitions.Def_GradedReserve_vbar
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The equilibrium probability of sale `s*(v) = min{(v/v̄)^p, 1}` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.1, p.5, PDF 6). -/
noncomputable def sStar (k : ℝ) (n : ℕ) (p v : ℝ) : ℝ := min ((v / vbar k n p) ^ p) 1

end GradedReserve


