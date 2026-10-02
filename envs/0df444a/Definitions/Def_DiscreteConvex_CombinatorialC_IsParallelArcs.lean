-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_IsParallelArcs
-- name    : DiscreteConvex_CombinatorialC_IsParallelArcs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:41:33.045347+00:00
-- url     : https://prove2.me/theorems/bc09fe37-cf38-4cb3-a86d-0ebf04b39a80
-- title:
--   Parallel arcs
-- statement:
--   Every simple cycle containing both arcs orients them oppositely.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSimpleCycle
import Definitions.Def_DiscreteConvex_CombinatorialC_Forward

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83: parallel arcs, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- Two arcs are **parallel**: every simple cycle containing both of them orients them in
opposite directions. -/
def IsParallelArcs {V A : Type*} [DecidableEq V] (src dst : A → V) (a b : A) : Prop :=
  ∀ k (v : Fin (k + 1) → V) (arcs : Fin (k + 1) → A), IsSimpleCycle src dst k v arcs →
    ∀ i j : Fin (k + 1), arcs i = a → arcs j = b →
      (Forward src v arcs i ↔ ¬ Forward src v arcs j)

end DiscreteConvex.CombinatorialC


