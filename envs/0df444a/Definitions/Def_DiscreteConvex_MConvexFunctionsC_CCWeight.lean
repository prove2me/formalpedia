-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_CCWeight
-- name    : DiscreteConvex_MConvexFunctionsC_CCWeight
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:38:39.107193+00:00
-- url     : https://prove2.me/theorems/67cf2d2b-6fd6-4aa1-9c1d-a60ea0b1f4d5
-- title:
--   CCWeight
-- statement:
--   The convex closure of $f$, linearly weighted by $p$: $\bar f(x) - \langle p,x\rangle$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting Theorem 6.43.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting Theorem 6.43

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureVal

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The convex closure of `f`, linearly weighted by `p` (i.e. the convex closure of `f[-p]`). -/
noncomputable def CCWeight (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) (x : V → ℝ) : WithTop ℝ :=
  ConvexClosureVal f x + (((-(∑ v, p v * x v) : ℝ)) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsC


