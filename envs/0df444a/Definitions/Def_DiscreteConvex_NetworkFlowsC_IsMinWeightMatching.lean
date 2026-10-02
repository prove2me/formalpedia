-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_IsMinWeightMatching
-- name    : DiscreteConvex_NetworkFlowsC_IsMinWeightMatching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:40.536067+00:00
-- url     : https://prove2.me/theorems/2195af27-7e38-413e-a993-c7ab25802e11
-- title:
--   IsMinWeightMatching
-- statement:
--   $M$ is a minimum-weight perfect matching.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, adjacent to Prop. 9.24.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, adjacent to Prop. 9.24

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_BipartiteMatching
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MatchingWeight

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def IsMinWeightMatching (Vp Vn : Finset V) (c : V → V → WithTop ℝ) (M : Finset (V × V)) : Prop :=
  BipartiteMatching Vp Vn M ∧
    ∀ M', BipartiteMatching Vp Vn M' → MatchingWeight c M ≤ MatchingWeight c M'

end DiscreteConvex.NetworkFlowsC


