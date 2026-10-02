-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_MConvexPolyhedron
-- name    : DiscreteConvex_LConvexFunctionsD_MConvexPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:03:54.774554+00:00
-- url     : https://prove2.me/theorems/af24c9fb-6185-4148-8c4f-ec41f8b973e4
-- title:
--   MConvexPolyhedron
-- statement:
--   A real M-convex polyhedron: the convex hull of an M-convex set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.108-116, adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.108-116, adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IntEmbed

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A real M-convex polyhedron: the convex hull of an M-convex set of integer vectors. -/
def MConvexPolyhedron (P : Set (V → ℝ)) : Prop :=
  ∃ B : Set (V → ℤ), ExchangeAxiomB B ∧ P = convexHull ℝ (IntEmbed B)

end DiscreteConvex.LConvexFunctionsD


