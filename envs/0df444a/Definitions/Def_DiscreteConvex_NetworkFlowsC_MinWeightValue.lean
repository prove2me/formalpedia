-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_MinWeightValue
-- name    : DiscreteConvex_NetworkFlowsC_MinWeightValue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:50.374432+00:00
-- url     : https://prove2.me/theorems/bbfd96e9-1867-4f65-a860-864a0e0641ba
-- title:
--   MinWeightValue
-- statement:
--   The minimum weight of a perfect matching, $+\infty$ if none exists.
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
/-- The minimum weight of a perfect matching, `+∞` if none exists. -/
noncomputable def MinWeightValue (Vp Vn : Finset V) (c : V → V → WithTop ℝ) : WithTop ℝ :=
  sInf {w : WithTop ℝ | ∃ M, BipartiteMatching Vp Vn M ∧ w = MatchingWeight c M}

end DiscreteConvex.NetworkFlowsC


