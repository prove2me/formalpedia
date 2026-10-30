-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_circValue
-- name    : FlowAllocationGames_UnitRanking_circValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:14:11.779762+00:00
-- url     : https://prove2.me/theorems/86dbb496-a720-4289-aa4b-7c3758202211
-- title:
--   Total flow value of a flow on $G'$
-- statement:
--   The **total flow value** of a flow $x$ on $G'$ is the sum of the flow on all edges of $G'$:
--
--   $$
--   \sum_{e \in E'} x_e = \sum_{e\in E} x_e + \sum_{v} x_{(v,s)} + \sum_v x_{(s,v)} .
--   $$
--
--   The proof of Theorem 9 starts from a circulation maximizing this value.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Circ

namespace FlowAllocationGames.UnitRanking

/-- **Total flow value of a flow on `G′`.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23: "an optimal circulation f∗ that maximizes the total flow value, i.e., it maximizes the sum
of flow on all edges", `Σ_{e∈E′} f∗e`.

`circValue x` is the sum of the flow on all edges of `G′`: the edges of `G`, the edges `(v, s)`
and the edges `(s, v)`. -/
def circValue {n m : ℕ} (x : Circ n m) : ℕ :=
  ∑ e, x.flow e + ∑ v, x.toS v + ∑ v, x.fromS v

end FlowAllocationGames.UnitRanking


