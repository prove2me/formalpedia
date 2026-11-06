-- Prove2me | Definitions.Def_GradedReserve_cxStar
-- name    : GradedReserve_cxStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:32.687183+00:00
-- url     : https://prove2.me/theorems/530a773a-827c-4af2-a695-87293e579cd7
-- title:
--   $c_x(t)$ at the candidate
-- statement:
--   $$c_x(t)=\frac N\ell\,c_0^N\,\bar v^{\,k}\,\frac m{p+\ell}\,t^{k/p},$$
--   the partial derivative of $c$ in $x$ at the candidate $(x^*(t),\widetilde M^*(t))$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, p.19 (PDF 20)

import Mathlib
import Definitions.Def_GradedReserve_powM
import Definitions.Def_GradedReserve_powL
import Definitions.Def_GradedReserve_powN
import Definitions.Def_GradedReserve_vbar
import Definitions.Def_GradedReserve_cZero
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `c_x(t) = (N/ℓ) c₀^N v̄^k (m/(p+ℓ)) t^{k/p}`, the partial derivative of `c` in `x` at the
candidate (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, p.19, PDF 20). -/
noncomputable def cxStar (k : ℝ) (n : ℕ) (p t : ℝ) : ℝ :=
  powN k n / powL k n * cZero k n p ^ powN k n * vbar k n p ^ k
    * (powM k n / (p + powL k n)) * t ^ (k / p)

end GradedReserve


