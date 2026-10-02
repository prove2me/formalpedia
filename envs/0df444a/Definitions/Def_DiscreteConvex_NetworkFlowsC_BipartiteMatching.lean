-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_BipartiteMatching
-- name    : DiscreteConvex_NetworkFlowsC_BipartiteMatching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:49:25.079289+00:00
-- url     : https://prove2.me/theorems/97c33662-d910-47bc-a16b-baf06752eab8
-- title:
--   BipartiteMatching
-- statement:
--   $M$ is a perfect matching between $V^+$ and $V^-$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, adjacent to Prop. 9.24.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, adjacent to Prop. 9.24

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `M` is a perfect matching between `Vp` and `Vn`. -/
def BipartiteMatching (Vp Vn : Finset V) (M : Finset (V × V)) : Prop :=
  (∀ p ∈ M, p.1 ∈ Vp ∧ p.2 ∈ Vn) ∧
  (∀ u ∈ Vp, ∃! v, (u, v) ∈ M) ∧ (∀ v ∈ Vn, ∃! u, (u, v) ∈ M)

end DiscreteConvex.NetworkFlowsC


