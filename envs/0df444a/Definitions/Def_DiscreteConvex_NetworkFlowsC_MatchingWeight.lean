-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_MatchingWeight
-- name    : DiscreteConvex_NetworkFlowsC_MatchingWeight
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:49:31.868491+00:00
-- url     : https://prove2.me/theorems/64faf75d-6aa8-4981-b6c5-52bf43008f4c
-- title:
--   MatchingWeight
-- statement:
--   The total weight of a matching.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, adjacent to Prop. 9.24.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, adjacent to Prop. 9.24

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def MatchingWeight (c : V → V → WithTop ℝ) (M : Finset (V × V)) : WithTop ℝ :=
  ∑ p ∈ M, c p.1 p.2

end DiscreteConvex.NetworkFlowsC


