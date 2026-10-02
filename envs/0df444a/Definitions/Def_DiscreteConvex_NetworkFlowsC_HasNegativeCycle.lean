-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_HasNegativeCycle
-- name    : DiscreteConvex_NetworkFlowsC_HasNegativeCycle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:54:10.327777+00:00
-- url     : https://prove2.me/theorems/6ec07732-ca48-4c28-9728-fa337ff9fd52
-- title:
--   HasNegativeCycle
-- statement:
--   There exists a negative-length cycle using only active arcs.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.265, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.265, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_IsCycle
import Definitions.Def_DiscreteConvex_NetworkFlowsC_CycleLength

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def HasNegativeCycle {Arc W : Type*} (tail head : Arc → W) (active : Arc → Prop)
    (l : Arc → WithTop ℝ) : Prop :=
  ∃ (k : ℕ) (a : Fin (k+1) → Arc), (∀ i, active (a i)) ∧ IsCycle tail head k a ∧
    CycleLength l k a < 0

end DiscreteConvex.NetworkFlowsC


