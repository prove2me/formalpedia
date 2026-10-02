-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_CharVec
-- name    : DiscreteConvex_MConvexFunctionsC_CharVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:11.240246+00:00
-- url     : https://prove2.me/theorems/4e81092c-f989-4ab5-8a9b-d8cab27cd0a7
-- title:
--   CharVec
-- statement:
--   The characteristic vector $\chi_u \in \mathbb Z^V$ of $u \in V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def CharVec (u : V) : V → ℤ := fun v => if v = u then 1 else 0

end DiscreteConvex.MConvexFunctionsC


