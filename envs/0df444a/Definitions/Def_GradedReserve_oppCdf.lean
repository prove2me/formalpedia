-- Prove2me | Definitions.Def_GradedReserve_oppCdf
-- name    : GradedReserve_oppCdf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:37.659926+00:00
-- url     : https://prove2.me/theorems/e48baa0c-2c80-486a-87a4-29f5c6832a93
-- title:
--   $Q=F^{n-1}$
-- statement:
--   For $n$ bidders, $Q(v)=F(v)^{n-1}$ is the probability that all $n-1$ opponents of a bidder have values at most $v$. In a symmetric equilibrium with increasing bids, a bidder of value $v$ outbids all opponents with probability $Q(v)$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, p.4 (PDF 5)

import Mathlib
import Definitions.Def_GradedReserve_valueCdf
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `Q = F^{n−1}` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, p.4, PDF 5): the probability that `n − 1` independent opponents
all have values at most `v`. -/
noncomputable def oppCdf (f : ℝ → ℝ) (n : ℕ) (v : ℝ) : ℝ := valueCdf f v ^ (n - 1)

end GradedReserve


