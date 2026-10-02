-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_TriangleInequality
-- name    : DiscreteConvex_MConvexFunctionsE_TriangleInequality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:03:59.82928+00:00
-- url     : https://prove2.me/theorems/0358f126-1507-4ba2-b288-e7532d009bd2
-- title:
--   TriangleInequality
-- statement:
--   The triangle inequality for a distance function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.2)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The triangle inequality for a distance function. -/
def TriangleInequality (γ : V → V → WithTop ℝ) : Prop :=
  ∀ v1 v2 v3, γ v1 v2 + γ v2 v3 ≥ γ v1 v3

end DiscreteConvex.MConvexFunctionsE


