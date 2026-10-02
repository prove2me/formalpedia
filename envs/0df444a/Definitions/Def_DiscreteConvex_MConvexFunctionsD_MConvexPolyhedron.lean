-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_MConvexPolyhedron
-- name    : DiscreteConvex_MConvexFunctionsD_MConvexPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:52:19.7341+00:00
-- url     : https://prove2.me/theorems/922a3904-6e26-4277-8da3-ef15fdc88985
-- title:
--   MConvexPolyhedron
-- statement:
--   A real M-convex polyhedron: the convex hull of an M-convex set of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.108-116, adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.108-116, adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IntEmbed

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def MConvexPolyhedron (P : Set (V → ℝ)) : Prop :=
  ∃ B : Set (V → ℤ), ExchangeAxiomB B ∧ P = convexHull ℝ (IntEmbed B)

end DiscreteConvex.MConvexFunctionsD


