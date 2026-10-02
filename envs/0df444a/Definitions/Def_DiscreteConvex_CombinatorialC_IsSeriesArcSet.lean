-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_IsSeriesArcSet
-- name    : DiscreteConvex_CombinatorialC_IsSeriesArcSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:44:38.038795+00:00
-- url     : https://prove2.me/theorems/243d0a17-621f-4a92-a2b3-e3fd1790d621
-- title:
--   Series arc set
-- statement:
--   A set of pairwise series arcs.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSeriesArcs

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83: a series arc set, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- A set of arcs is **series** if it consists of pairwise series arcs. -/
def IsSeriesArcSet {V A : Type*} [DecidableEq V] [DecidableEq A] (src dst : A → V)
    (S : Finset A) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → IsSeriesArcs src dst a b

end DiscreteConvex.CombinatorialC


