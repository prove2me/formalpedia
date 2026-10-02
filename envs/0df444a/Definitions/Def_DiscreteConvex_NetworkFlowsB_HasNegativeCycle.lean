-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_HasNegativeCycle
-- name    : DiscreteConvex_NetworkFlowsB_HasNegativeCycle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:23:35.169987+00:00
-- url     : https://prove2.me/theorems/37737820-d5ba-4fb5-8627-b02c655f1004
-- title:
--   HasNegativeCycle
-- statement:
--   There exists a negative-length cycle using only active arcs.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.251-252, the negative-cycle definition preceding Theorem 9.5.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.251-252, the negative-cycle definition preceding Theorem 9.5

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsCycle
import Definitions.Def_DiscreteConvex_NetworkFlowsB_CycleLength

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- There exists a negative-length cycle using only `active` arcs. -/
def HasNegativeCycle {Arc W : Type*} (tail head : Arc → W) (active : Arc → Prop)
    (l : Arc → WithTop ℝ) : Prop :=
  ∃ (k : ℕ) (a : Fin (k+1) → Arc), (∀ i, active (a i)) ∧ IsCycle tail head k a ∧
    CycleLength l k a < 0

end DiscreteConvex.NetworkFlowsB


