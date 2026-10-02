-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsMultipleOfOne
-- name    : DiscreteConvex_LConvexFunctionsD_IsMultipleOfOne
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:54.863003+00:00
-- url     : https://prove2.me/theorems/5356e20b-a53d-4e19-9862-74ca4fa5f860
-- title:
--   IsMultipleOfOne
-- statement:
--   $q$ is $p$ plus a multiple of the all-ones vector.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.201, supporting Theorem 7.53.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.201, supporting Theorem 7.53

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `q` is `p` plus a multiple of the all-ones vector. -/
def IsMultipleOfOne (p q : V → ℤ) : Prop := ∃ k : ℤ, q = fun v => p v + k

end DiscreteConvex.LConvexFunctionsD


