-- Prove2me | Definitions.Def_GradedReserve_cMStar
-- name    : GradedReserve_cMStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:41.13484+00:00
-- url     : https://prove2.me/theorems/c696d744-b849-416a-acc5-e497bfdc18f7
-- title:
--   $c_{\widetilde M}(t)$ at the candidate
-- statement:
--   $$c_{\widetilde M}(t)=\frac N\ell\,c_0^N\,\bar v^{\,k}\,t^{k/p},$$
--   the partial derivative of $c$ in $\widetilde M$ at the candidate $(x^*(t),\widetilde M^*(t))$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, p.19 (PDF 20)

import Mathlib
import Definitions.Def_GradedReserve_powL
import Definitions.Def_GradedReserve_powN
import Definitions.Def_GradedReserve_vbar
import Definitions.Def_GradedReserve_cZero
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `c_M̃(t) = (N/ℓ) c₀^N v̄^k t^{k/p}`, the partial derivative of `c` in `M̃` at the candidate
(Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, p.19, PDF 20). -/
noncomputable def cMStar (k : ℝ) (n : ℕ) (p t : ℝ) : ℝ :=
  powN k n / powL k n * cZero k n p ^ powN k n * vbar k n p ^ k * t ^ (k / p)

end GradedReserve


