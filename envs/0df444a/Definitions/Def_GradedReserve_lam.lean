-- Prove2me | Definitions.Def_GradedReserve_lam
-- name    : GradedReserve_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:30.158058+00:00
-- url     : https://prove2.me/theorems/6a80d15d-7443-49be-a84d-e67d5460b395
-- title:
--   Multiplier $\Lambda=c_0^N\bar v^kp$, display (28)
-- statement:
--   $$\Lambda=c_0^{N}\,\bar v^{\,k}\,p .$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, display (28), p.19 (PDF 20)

import Mathlib
import Definitions.Def_GradedReserve_powN
import Definitions.Def_GradedReserve_vbar
import Definitions.Def_GradedReserve_cZero
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The multiplier `Λ = c₀^N v̄^k p` of display (28) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, (28), p.19, PDF 20). -/
noncomputable def lam (k : ℝ) (n : ℕ) (p : ℝ) : ℝ := cZero k n p ^ powN k n * vbar k n p ^ k * p

end GradedReserve


