-- Prove2me | Definitions.Def_GradedReserve_powM
-- name    : GradedReserve_powM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:49.858556+00:00
-- url     : https://prove2.me/theorems/eb0cbb4e-a67e-45f7-8048-0d8d631df1db
-- title:
--   $m=k(n-1)$
-- statement:
--   For the power law $F(v)=v^k$ and $n$ bidders, $m=k(n-1)$; then $Q(v)=v^m$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.1, p.5 (PDF 6)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `m = k(n − 1)` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.1, p.5, PDF 6). -/
def powM (k : ℝ) (n : ℕ) : ℝ := k * ((n : ℝ) - 1)

end GradedReserve


