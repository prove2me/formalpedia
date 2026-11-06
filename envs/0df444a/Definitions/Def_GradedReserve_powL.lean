-- Prove2me | Definitions.Def_GradedReserve_powL
-- name    : GradedReserve_powL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:53.795839+00:00
-- url     : https://prove2.me/theorems/4c10fca1-902c-4d22-be74-35786d608b62
-- title:
--   $\ell=m+1$
-- statement:
--   $\ell=m+1=k(n-1)+1$; then $H(v)=v^\ell/\ell$ for the power law.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.1, p.5 (PDF 6)

import Mathlib
import Definitions.Def_GradedReserve_powM
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `ℓ = m + 1` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.1, p.5, PDF 6). -/
def powL (k : ℝ) (n : ℕ) : ℝ := powM k n + 1

end GradedReserve


