-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_MConvexPolyhedron
-- name    : DiscreteConvex_MConvexFunctionsC_MConvexPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:29:37.286589+00:00
-- url     : https://prove2.me/theorems/bb6133f7-d174-49ca-a48f-cc29973c12ae
-- title:
--   MConvexPolyhedron
-- statement:
--   A real **M-convex polyhedron**: the convex hull of an M-convex set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.108-116, adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.108-116, adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IntEmbed

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A real M-convex polyhedron: the convex hull of an M-convex set of integer vectors. -/
def MConvexPolyhedron (P : Set (V → ℝ)) : Prop :=
  ∃ B : Set (V → ℤ), ExchangeAxiomB B ∧ P = convexHull ℝ (IntEmbed B)

end DiscreteConvex.MConvexFunctionsC


