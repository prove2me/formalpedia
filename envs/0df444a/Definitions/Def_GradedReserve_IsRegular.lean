-- Prove2me | Definitions.Def_GradedReserve_IsRegular
-- name    : GradedReserve_IsRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:07.614365+00:00
-- url     : https://prove2.me/theorems/d0143d02-081e-4142-88ed-5b2635d6bb23
-- title:
--   Regular value law: $\varphi$ strictly increasing
-- statement:
--   The value law is **regular** if its virtual value $\varphi$ is strictly increasing.
--
--   Regularity is the standing assumption of Section 3; it makes the reserve-price revenue curve $R_n$ single-peaked at the crossing point $r^*$.
--
--   **Formalization Note** Strict monotonicity is required on $(0,1)$, where $f>0$ and $\varphi$ is defined.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, p.4 (PDF 5); Section 3, p.5 (PDF 6)

import Mathlib
import Definitions.Def_GradedReserve_virtualValue
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- Regularity (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, p.4, PDF 5): "F is regular if φ is strictly increasing".

**Formalization Note.** Strict monotonicity is required on `(0, 1)`, where `f > 0` and `φ` is
defined; at `v = 0` the density may vanish (e.g. `f(v) = k v^{k−1}` with `k > 1`) and `φ(0)` is
undefined in the paper. -/
def IsRegular (f : ℝ → ℝ) : Prop := StrictMonoOn (virtualValue f) (Ioo 0 1)

end GradedReserve


