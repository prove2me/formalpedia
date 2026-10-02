-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_UniqueMinConditionPair
-- name    : DiscreteConvex_NetworkFlowsC_UniqueMinConditionPair
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:03:39.707382+00:00
-- url     : https://prove2.me/theorems/0e38a759-a0a7-4718-b3da-2333c8cb781e
-- title:
--   UniqueMinConditionPair
-- statement:
--   $(x,y)$ satisfies the unique-min condition.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, the unique-min condition.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, the unique-min condition

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppPos
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppNeg
import Definitions.Def_DiscreteConvex_NetworkFlowsC_IsMinWeightMatching
import Definitions.Def_DiscreteConvex_NetworkFlowsC_UMWeight
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MinWeightValue

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `(x,y)` satisfies the unique-min condition. The book's condition is about matchings inside
`E`, so the minimum weight must be finite: `UMWeight` is `+∞` off `E`, and a single matching of
weight `+∞` would otherwise count as the unique minimum (with `f` the indicator of `0`, `x = 0`
and `y = -χu + χv`, `E` is empty and the conclusion `y ∈ dom f` is false). -/
def UniqueMinConditionPair (f : (V → ℤ) → WithTop ℝ) (x y : V → ℤ) : Prop :=
  (∃! M, IsMinWeightMatching (SuppPos x y) (SuppNeg x y) (UMWeight f x) M) ∧
    MinWeightValue (SuppPos x y) (SuppNeg x y) (UMWeight f x) ≠ ⊤

end DiscreteConvex.NetworkFlowsC


