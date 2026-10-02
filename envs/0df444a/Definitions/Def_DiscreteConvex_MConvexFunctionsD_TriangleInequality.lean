-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_TriangleInequality
-- name    : DiscreteConvex_MConvexFunctionsD_TriangleInequality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:49:14.13629+00:00
-- url     : https://prove2.me/theorems/795668d1-1d63-44e3-a1f4-ea9f4eb66fbb
-- title:
--   TriangleInequality
-- statement:
--   The triangle inequality for a distance function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.2)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The triangle inequality (5.2). -/
def TriangleInequality (γ : V → V → WithTop ℝ) : Prop :=
  ∀ v1 v2 v3, γ v1 v2 + γ v2 v3 ≥ γ v1 v3

end DiscreteConvex.MConvexFunctionsD


