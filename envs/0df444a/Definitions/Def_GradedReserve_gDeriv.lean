-- Prove2me | Definitions.Def_GradedReserve_gDeriv
-- name    : GradedReserve_gDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:50.981854+00:00
-- url     : https://prove2.me/theorems/77b8f18a-311c-4c2b-8bbb-b9e3a22d0fe0
-- title:
--   $g'(x)=\frac n\ell(1-(k+1)x^{k/\ell})$
-- statement:
--   $$g'(x)=\frac n\ell\big(1-(k+1)\,x^{k/\ell}\big).$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, p.18 (PDF 19)

import Mathlib
import Definitions.Def_GradedReserve_powL
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `g′(x) = (n/ℓ)(1 − (k+1) x^{k/ℓ})` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, p.18, PDF 19). -/
noncomputable def gDeriv (k : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (n / powL k n) * (1 - (k + 1) * x ^ (k / powL k n))

end GradedReserve


