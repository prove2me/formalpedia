-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNatConvexPolyhedron
-- name    : DiscreteConvex_LConvexFunctionsC_LNatConvexPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:38:35.009927+00:00
-- url     : https://prove2.me/theorems/358e3d67-4c1f-40e6-8dd7-42cc391fc4d2
-- title:
--   LNatConvexPolyhedron
-- statement:
--   A real L$^\natural$-convex polyhedron: the convex hull of an L$^\natural$-convex set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.191, class analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.191, class analogue

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNatConvexSet
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IntEmbed

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A real L♮-convex polyhedron: the convex hull of an L♮-convex set of integer vectors. -/
def LNatConvexPolyhedron (P : Set (V → ℝ)) : Prop :=
  ∃ D : Set (V → ℤ), LNatConvexSet D ∧ P = convexHull ℝ (IntEmbed D)

end DiscreteConvex.LConvexFunctionsC


