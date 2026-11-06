-- Prove2me | Definitions.Def_GradedReserve_powN
-- name    : GradedReserve_powN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:47.273634+00:00
-- url     : https://prove2.me/theorems/25ff4fbe-f14f-4f54-ad15-4e33506f1c88
-- title:
--   $N=kn$
-- statement:
--   $N=kn$; for the power law the highest of $n$ values has distribution $v^N$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.1, p.5 (PDF 6)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `N = kn` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.1, p.5, PDF 6). -/
def powN (k : ℝ) (n : ℕ) : ℝ := k * n

end GradedReserve


