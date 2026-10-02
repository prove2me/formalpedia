-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegralPolyhedron
-- name    : DiscreteConvex_LConvexFunctionsD_IsIntegralPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:19.891559+00:00
-- url     : https://prove2.me/theorems/9767f3c4-3847-4aeb-8166-426c4b31a588
-- title:
--   IsIntegralPolyhedron
-- statement:
--   A polyhedron equal to the convex hull of its integer points.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A polyhedron equal to the convex hull of its integer points. -/
def IsIntegralPolyhedron (P : Set (V → ℝ)) : Prop :=
  P = convexHull ℝ (P ∩ {x : V → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)})

end DiscreteConvex.LConvexFunctionsD


