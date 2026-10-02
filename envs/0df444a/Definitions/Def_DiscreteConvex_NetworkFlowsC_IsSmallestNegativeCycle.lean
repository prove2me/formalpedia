-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_IsSmallestNegativeCycle
-- name    : DiscreteConvex_NetworkFlowsC_IsSmallestNegativeCycle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:54:22.482989+00:00
-- url     : https://prove2.me/theorems/3b22ebf3-6d06-45c5-b11c-836c5c50c777
-- title:
--   IsSmallestNegativeCycle
-- statement:
--   A negative cycle with the smallest number of arcs among negative cycles.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.265, preceding Theorem 9.22.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.265, preceding Theorem 9.22

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_IsCycle
import Definitions.Def_DiscreteConvex_NetworkFlowsC_CycleLength

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `a` is a negative cycle with the smallest number of arcs among negative cycles. -/
def IsSmallestNegativeCycle {Arc W : Type*} (tail head : Arc → W) (active : Arc → Prop)
    (l : Arc → WithTop ℝ) (k : ℕ) (a : Fin (k+1) → Arc) : Prop :=
  (∀ i, active (a i)) ∧ IsCycle tail head k a ∧ CycleLength l k a < 0 ∧
  ∀ (k' : ℕ) (a' : Fin (k'+1) → Arc), (∀ i, active (a' i)) → IsCycle tail head k' a' →
    CycleLength l k' a' < 0 → k ≤ k'

end DiscreteConvex.NetworkFlowsC


