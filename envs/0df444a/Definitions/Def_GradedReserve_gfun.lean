-- Prove2me | Definitions.Def_GradedReserve_gfun
-- name    : GradedReserve_gfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:09.069207+00:00
-- url     : https://prove2.me/theorems/acef1358-9954-493b-bf6e-e8bfbd883b85
-- title:
--   $g(x)=\frac n\ell x-\frac{n(k+1)}{N+1}x^{(N+1)/\ell}$
-- statement:
--   $$g(x)=\frac n\ell\,x-\frac{n(k+1)}{N+1}\,x^{(N+1)/\ell},$$
--   the rational revenue of a level, in the variable $x=w^\ell$, beyond $R_n(0)$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, display (24), p.18 (PDF 19)

import Mathlib
import Definitions.Def_GradedReserve_powL
import Definitions.Def_GradedReserve_powN
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `g(x) = (n/ℓ) x − (n(k+1)/(N+1)) x^{(N+1)/ℓ}` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, (24), p.18, PDF 19). -/
noncomputable def gfun (k : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (n / powL k n) * x - (n * (k + 1) / (powN k n + 1)) * x ^ ((powN k n + 1) / powL k n)

end GradedReserve


