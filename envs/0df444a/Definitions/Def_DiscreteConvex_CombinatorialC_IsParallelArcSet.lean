-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_IsParallelArcSet
-- name    : DiscreteConvex_CombinatorialC_IsParallelArcSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:44:19.001538+00:00
-- url     : https://prove2.me/theorems/79af29cf-84d8-42e6-b3d6-1063c69381e4
-- title:
--   Parallel arc set
-- statement:
--   A set of pairwise parallel arcs.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsParallelArcs

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83: a parallel arc set, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- A set of arcs is **parallel** if it consists of pairwise parallel arcs. -/
def IsParallelArcSet {V A : Type*} [DecidableEq V] [DecidableEq A] (src dst : A → V)
    (P : Finset A) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, a ≠ b → IsParallelArcs src dst a b

end DiscreteConvex.CombinatorialC


