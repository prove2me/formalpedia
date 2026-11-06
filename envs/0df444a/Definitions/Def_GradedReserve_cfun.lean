-- Prove2me | Definitions.Def_GradedReserve_cfun
-- name    : GradedReserve_cfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:50.93626+00:00
-- url     : https://prove2.me/theorems/019cecdc-4369-4ec6-8878-bfbe57800b04
-- title:
--   Anchored-loss integrand $c(x,\widetilde M)=\frac N{N+1}B^{N+1}$
-- statement:
--   $$c(x,\widetilde M)=\frac N{N+1}\,B(x,\widetilde M)^{N+1},$$
--   with $c(0,0)=0$, read on the feasible wedge $0\le\widetilde M\le x$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, display (25), p.18 (PDF 19)

import Mathlib
import Definitions.Def_GradedReserve_powN
import Definitions.Def_GradedReserve_bidX
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The anchored-loss integrand `c(x, M̃) = (N/(N+1)) B(x, M̃)^{N+1}` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, (25), p.18,
PDF 19), with `c(0, 0) = 0`. Read on the wedge `0 ≤ M̃ ≤ x`, where `B ≥ 0`. -/
noncomputable def cfun (k : ℝ) (n : ℕ) (x Mt : ℝ) : ℝ :=
  powN k n / (powN k n + 1) * bidX k n x Mt ^ (powN k n + 1)

end GradedReserve


