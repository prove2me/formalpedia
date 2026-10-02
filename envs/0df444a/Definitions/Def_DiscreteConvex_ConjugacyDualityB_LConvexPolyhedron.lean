-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_LConvexPolyhedron
-- name    : DiscreteConvex_ConjugacyDualityB_LConvexPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:31:32.708065+00:00
-- url     : https://prove2.me/theorems/9dec7e17-facd-4ca2-b659-3420cdc28a15
-- title:
--   LConvexPolyhedron
-- statement:
--   A real L-convex polyhedron.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.191, class $L[\\mathbb Z|\\mathbb R\\to\\mathbb R]$-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.191, class $L[\\mathbb Z|\\mathbb R\\to\\mathbb R]$-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IntEmbed
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LConvexSet

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A real L-convex polyhedron. -/
def LConvexPolyhedron (P : Set (V → ℝ)) : Prop :=
  ∃ D : Set (V → ℤ), LConvexSet D ∧ P = convexHull ℝ (IntEmbed D)

end DiscreteConvex.ConjugacyDualityB


