-- Prove2me | Definitions.Def_GradedReserve_bidX
-- name    : GradedReserve_bidX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:41.885198+00:00
-- url     : https://prove2.me/theorems/66d4e015-54d0-4f61-b04e-19df09327458
-- title:
--   Level bid $B(x,\widetilde M)$ for power laws, display (23)
-- statement:
--   For the power law, in the variables $x=w^\ell$ and $\widetilde M=\ell M$, the level bid (4) becomes
--   $$B(x,\widetilde M)=\frac{m x+\widetilde M}{\ell\,x^{m/\ell}},$$
--   with $B(0,0)=0$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, display (23), p.18 (PDF 19)

import Mathlib
import Definitions.Def_GradedReserve_powM
import Definitions.Def_GradedReserve_powL
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The level bid in the variables `x = w^ℓ`, `M̃ = ℓ M` for the power law, display (23) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission),
Section A.5, (23), p.18, PDF 19): `B(x, M̃) = (m x + M̃)/(ℓ x^{m/ℓ})`, with `B(0, 0) = 0`.

**Formalization Note.** At `x = 0` the value is `0` (the paper's convention `c(0, 0) = 0` and
`B(t) = 0` if `w(t) = 0`). -/
noncomputable def bidX (k : ℝ) (n : ℕ) (x Mt : ℝ) : ℝ :=
  if x = 0 then 0 else (powM k n * x + Mt) / (powL k n * x ^ (powM k n / powL k n))

end GradedReserve


