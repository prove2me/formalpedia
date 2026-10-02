-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
-- name    : DiscreteConvex_MConvexFunctionsE_CharVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:03:21.166794+00:00
-- url     : https://prove2.me/theorems/c4113b63-8ccf-421e-8031-35355f2e0435
-- title:
--   CharVec
-- statement:
--   The characteristic vector $\chi_u \in \mathbb Z^V$ of $u \in V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The characteristic vector of `v`. -/
def CharVec (v : V) : V → ℤ := fun w => if w = v then 1 else 0

end DiscreteConvex.MConvexFunctionsE


