-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_LConvexPolyhedron
-- name    : DiscreteConvex_LConvexFunctionsC_LConvexPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:34:53.04785+00:00
-- url     : https://prove2.me/theorems/2a29d0de-37f8-40e3-85bd-cf478f392e06
-- title:
--   LConvexPolyhedron
-- statement:
--   A real L-convex polyhedron: the convex hull of an L-convex set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.191, class $L[\\mathbb Z|\\mathbb R\\to\\mathbb R]$-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.191, class $L[\\mathbb Z|\\mathbb R\\to\\mathbb R]$-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IntEmbed

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A real L-convex polyhedron: the convex hull of an L-convex set of integer vectors. -/
def LConvexPolyhedron (P : Set (V → ℝ)) : Prop :=
  ∃ D : Set (V → ℤ), LConvexSet D ∧ P = convexHull ℝ (IntEmbed D)

end DiscreteConvex.LConvexFunctionsC


