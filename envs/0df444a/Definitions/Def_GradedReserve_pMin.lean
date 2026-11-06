-- Prove2me | Definitions.Def_GradedReserve_pMin
-- name    : GradedReserve_pMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:16.27219+00:00
-- url     : https://prove2.me/theorems/7aaf0a5b-3135-4b26-a057-a7e3911928c2
-- title:
--   $p_{\min}=\tfrac12(\sqrt{\ell^2+4km}-\ell)$
-- statement:
--   The lower end of the parameter range of Theorem 3.1,
--   $$p_{\min}=\frac{\sqrt{\ell^2+4km}-\ell}{2},$$
--   the positive root of $p(p+\ell)=km$. For $p>p_{\min}$ the quantity $\bar v$ below is positive.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.1, p.5 (PDF 6); display (26), p.18 (PDF 19)

import Mathlib
import Definitions.Def_GradedReserve_powM
import Definitions.Def_GradedReserve_powL
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `p_min = (√(ℓ² + 4km) − ℓ)/2` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.1, p.5, PDF 6; display (26), p.18, PDF 19). -/
noncomputable def pMin (k : ℝ) (n : ℕ) : ℝ :=
  (Real.sqrt (powL k n ^ 2 + 4 * k * powM k n) - powL k n) / 2

end GradedReserve


