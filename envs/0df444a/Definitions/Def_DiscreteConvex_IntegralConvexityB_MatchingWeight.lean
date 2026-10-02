-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_MatchingWeight
-- name    : DiscreteConvex_IntegralConvexityB_MatchingWeight
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:00:00.264229+00:00
-- url     : https://prove2.me/theorems/dce48575-ebd2-427e-b753-bf5d99ba40b2
-- title:
--   Weight of a perfect matching
-- statement:
--   $\sum_u c(u,\sigma u)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.109.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.109

import Mathlib

/-!
The total weight of a perfect matching (Murota, *Discrete Convex Analysis*, SIAM 2003, p.109),
in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- The weight `∑_u c(u, σ u)` of the perfect matching represented by `σ`. -/
noncomputable def MatchingWeight {Vp Vm : Type*} [Fintype Vp] (c : Vp × Vm → WithTop ℝ)
    (sigma : Vp ≃ Vm) : WithTop ℝ :=
  ∑ u, c (u, sigma u)

end DiscreteConvex.IntegralConvexityB


