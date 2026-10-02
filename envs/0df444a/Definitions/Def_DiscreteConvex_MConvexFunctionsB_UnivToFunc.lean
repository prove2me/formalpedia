-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_UnivToFunc
-- name    : DiscreteConvex_MConvexFunctionsB_UnivToFunc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:06:13.849031+00:00
-- url     : https://prove2.me/theorems/e8c3cfa3-038f-4865-b9b5-bd910afea33a
-- title:
--   UnivToFunc
-- statement:
--   A univariate function viewed as a function of one coordinate.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.140, supporting Proposition 6.9.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.140, supporting Proposition 6.9

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.140, supporting Proposition 6.9, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- A univariate function viewed as a function of one `Unit`-indexed coordinate. -/
def UnivToFunc (psi : ℤ → WithTop ℝ) : (Unit → ℤ) → WithTop ℝ := fun x => psi (x ())

end DiscreteConvex.MConvexFunctionsB


