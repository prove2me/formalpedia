-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexPolyhedron
-- name    : DiscreteConvex_LConvexFunctionsD_LConvexPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:02:48.257015+00:00
-- url     : https://prove2.me/theorems/b84af694-3740-4a66-83ae-4a7c040e3ef4
-- title:
--   LConvexPolyhedron
-- statement:
--   A real L-convex polyhedron: the convex hull of an L-convex set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.191, class $L[\\mathbb Z|\\mathbb R\\to\\mathbb R]$-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.191, class $L[\\mathbb Z|\\mathbb R\\to\\mathbb R]$-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IntEmbed
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexSet

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A real L-convex polyhedron: the convex hull of an L-convex set of integer vectors. -/
def LConvexPolyhedron (P : Set (V → ℝ)) : Prop :=
  ∃ D : Set (V → ℤ), LConvexSet D ∧ P = convexHull ℝ (IntEmbed D)

end DiscreteConvex.LConvexFunctionsD


