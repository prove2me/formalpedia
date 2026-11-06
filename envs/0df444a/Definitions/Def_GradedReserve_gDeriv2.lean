-- Prove2me | Definitions.Def_GradedReserve_gDeriv2
-- name    : GradedReserve_gDeriv2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:37.304288+00:00
-- url     : https://prove2.me/theorems/44131a62-9b79-4a60-8892-73824e30bf52
-- title:
--   $g''(x)=-\frac{nk(k+1)}{\ell^2}x^{k/\ell-1}$
-- statement:
--   $$g''(x)=-\frac{nk(k+1)}{\ell^2}\,x^{k/\ell-1}.$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, p.18 (PDF 19)

import Mathlib
import Definitions.Def_GradedReserve_powL
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `g″(x) = −(nk(k+1)/ℓ²) x^{k/ℓ−1}` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, p.18, PDF 19). -/
noncomputable def gDeriv2 (k : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  -(n * k * (k + 1) / powL k n ^ 2) * x ^ (k / powL k n - 1)

end GradedReserve


