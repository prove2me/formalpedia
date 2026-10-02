-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_IsSeriesArcs
-- name    : DiscreteConvex_CombinatorialC_IsSeriesArcs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:41:44.826116+00:00
-- url     : https://prove2.me/theorems/92bda83f-3327-4928-8a31-7be21a0be5aa
-- title:
--   Series arcs
-- statement:
--   Every simple cycle containing both arcs orients them the same way.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSimpleCycle
import Definitions.Def_DiscreteConvex_CombinatorialC_Forward

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83: series arcs, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- Two arcs are **series**: every simple cycle containing both of them orients them in the
same direction. -/
def IsSeriesArcs {V A : Type*} [DecidableEq V] (src dst : A → V) (a b : A) : Prop :=
  ∀ k (v : Fin (k + 1) → V) (arcs : Fin (k + 1) → A), IsSimpleCycle src dst k v arcs →
    ∀ i j : Fin (k + 1), arcs i = a → arcs j = b →
      (Forward src v arcs i ↔ Forward src v arcs j)

end DiscreteConvex.CombinatorialC


