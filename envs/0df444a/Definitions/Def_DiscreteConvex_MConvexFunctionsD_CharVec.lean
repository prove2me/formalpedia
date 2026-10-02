-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_CharVec
-- name    : DiscreteConvex_MConvexFunctionsD_CharVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:46:48.336351+00:00
-- url     : https://prove2.me/theorems/e7c1d124-6c0f-4c09-b567-5f3246581c8d
-- title:
--   CharVec
-- statement:
--   The characteristic vector $\chi_u \in \mathbb Z^V$ of $u \in V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def CharVec (u : V) : V → ℤ := fun v => if v = u then 1 else 0

end DiscreteConvex.MConvexFunctionsD


