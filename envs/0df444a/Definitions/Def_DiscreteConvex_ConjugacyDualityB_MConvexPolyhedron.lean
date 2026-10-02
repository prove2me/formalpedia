-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_MConvexPolyhedron
-- name    : DiscreteConvex_ConjugacyDualityB_MConvexPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:33:10.071387+00:00
-- url     : https://prove2.me/theorems/d4342e5c-b087-4f46-b1e0-7c754ae973a6
-- title:
--   MConvexPolyhedron
-- statement:
--   A real M-convex polyhedron.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.108-116, adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.108-116, adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IntEmbed

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A real M-convex polyhedron. -/
def MConvexPolyhedron (P : Set (V → ℝ)) : Prop :=
  ∃ B : Set (V → ℤ), ExchangeAxiomB B ∧ P = convexHull ℝ (IntEmbed B)

end DiscreteConvex.ConjugacyDualityB


