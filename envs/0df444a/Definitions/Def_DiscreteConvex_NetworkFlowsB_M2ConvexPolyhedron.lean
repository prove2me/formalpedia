-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_M2ConvexPolyhedron
-- name    : DiscreteConvex_NetworkFlowsB_M2ConvexPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:27:21.079935+00:00
-- url     : https://prove2.me/theorems/e82dc819-340a-443d-831d-47b139bb3935
-- title:
--   M2ConvexPolyhedron
-- statement:
--   A real M2-convex polyhedron: the convex hull of an M2-convex set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.107/226, polyhedron analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.107/226, polyhedron analogue

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_M2ConvexSet
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IntEmbed

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- A real M2-convex polyhedron: the convex hull of an M2-convex set of integer vectors. -/
def M2ConvexPolyhedron (P : Set (V → ℝ)) : Prop :=
  ∃ D : Set (V → ℤ), M2ConvexSet D ∧ P = convexHull ℝ (IntEmbed D)

end DiscreteConvex.NetworkFlowsB


