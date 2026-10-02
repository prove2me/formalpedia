-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_LiftedSet
-- name    : DiscreteConvex_MConvexFunctionsC_LiftedSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:23.555611+00:00
-- url     : https://prove2.me/theorems/eb7ea64b-8c90-4742-b4fe-5b4fbabe0e4e
-- title:
--   LiftedSet
-- statement:
--   The lift of a set $D \subseteq \mathbb Z^V$ to $\tilde V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.121.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.121

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def LiftedSet (D : Set (V → ℤ)) : Set (Option V → ℤ) :=
  {x | x none = -(∑ v : V, x (some v)) ∧ (fun v => x (some v)) ∈ D}

end DiscreteConvex.MConvexFunctionsC


