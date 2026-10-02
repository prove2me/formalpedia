-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatConvexPolyhedron
-- name    : DiscreteConvex_MConvexFunctionsC_MNatConvexPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:39:00.801087+00:00
-- url     : https://prove2.me/theorems/da56e182-17f2-4b4f-b3ae-a76a4479375f
-- title:
--   MNatConvexPolyhedron
-- statement:
--   A real **M$^\natural$-convex polyhedron**: the convex hull of an M$^\natural$-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.121, adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.121, adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatConvexSet
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IntEmbed

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A real M♮-convex polyhedron: the convex hull of an M♮-convex set. -/
def MNatConvexPolyhedron (P : Set (V → ℝ)) : Prop :=
  ∃ D : Set (V → ℤ), MNatConvexSet D ∧ P = convexHull ℝ (IntEmbed D)

end DiscreteConvex.MConvexFunctionsC


