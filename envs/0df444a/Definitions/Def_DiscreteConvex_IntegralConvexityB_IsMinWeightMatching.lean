-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_IsMinWeightMatching
-- name    : DiscreteConvex_IntegralConvexityB_IsMinWeightMatching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:02:33.991888+00:00
-- url     : https://prove2.me/theorems/fc0402a8-a8a5-4e52-8b06-1baadef32c61
-- title:
--   Minimum-weight perfect matching
-- statement:
--   A perfect matching minimizing `MatchingWeight`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.109.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.109

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPerfectMatchingBij
import Definitions.Def_DiscreteConvex_IntegralConvexityB_MatchingWeight

/-!
A minimum-weight perfect matching (Murota, *Discrete Convex Analysis*, SIAM 2003, p.109), in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `σ` is a **minimum-weight perfect matching** of `(Vp, Vm; E)` for cost `c`. -/
def IsMinWeightMatching {Vp Vm : Type*} [Fintype Vp] (E : Set (Vp × Vm)) (c : Vp × Vm → WithTop ℝ)
    (sigma : Vp ≃ Vm) : Prop :=
  IsPerfectMatchingBij E sigma ∧
    ∀ tau : Vp ≃ Vm, IsPerfectMatchingBij E tau → MatchingWeight c sigma ≤ MatchingWeight c tau

end DiscreteConvex.IntegralConvexityB


