-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_LConvexPolyhedron
-- name    : DiscreteConvex_NetworkFlowsB_LConvexPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:23:00.961325+00:00
-- url     : https://prove2.me/theorems/a4a39440-ac33-4cb4-bbc2-fcde8e4d2cac
-- title:
--   LConvexPolyhedron
-- statement:
--   A real L-convex polyhedron: the convex hull of an L-convex set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_LConvexSet
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IntEmbed

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- A real L-convex polyhedron: the convex hull of an L-convex set of integer vectors. -/
def LConvexPolyhedron (P : Set (V → ℝ)) : Prop :=
  ∃ D : Set (V → ℤ), LConvexSet D ∧ P = convexHull ℝ (IntEmbed D)

end DiscreteConvex.NetworkFlowsB


