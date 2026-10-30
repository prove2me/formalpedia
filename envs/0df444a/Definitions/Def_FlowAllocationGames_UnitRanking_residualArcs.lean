-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_residualArcs
-- name    : FlowAllocationGames_UnitRanking_residualArcs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:26:21.860132+00:00
-- url     : https://prove2.me/theorems/d0df4f51-1a93-4348-ac9b-d0070eb8289c
-- title:
--   Residual network of a flow on $G'$
-- statement:
--   For a flow $x$ on $G'$, every edge $j$ with $x_j < \mathrm{cap}_j$ gives a forward arc $\mathrm{tail}(j) \to \mathrm{head}(j)$ of cost $-1$, and every edge with $x_j > 0$ gives a backward arc $\mathrm{head}(j) \to \mathrm{tail}(j)$ of cost $+1$. Since every edge has cost $-1$ per unit, a minimum-cost circulation of $G'$ is a circulation of maximum total flow value.
--
--   This is part of the witness algorithm of the mission: the paper computes the optimal circulation $f^*$ by citing Tardos [45] and fixes no algorithm.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Cost
import Definitions.Def_FlowAllocationGames_UnitRanking_tick
import Definitions.Def_FlowAllocationGames_UnitRanking_zlt
import Definitions.Def_FlowAllocationGames_UnitRanking_Net
import Definitions.Def_FlowAllocationGames_UnitRanking_ResArc

namespace FlowAllocationGames.UnitRanking

/-- **The residual network of a flow on `G′`.**
Witness algorithm of the mission for "f∗ can be computed in strongly polynomial time [45]" in
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23.

For each edge `j` of `G` with flow `x[j]` and capacity `cap[j]`: a forward arc `tl[j] → hd[j]`
of cost `-1` if `x[j] < cap[j]`, and a backward arc `hd[j] → tl[j]` of cost `+1` if `x[j] > 0`.

**Formalization Note.** Every edge of `G′` has cost `-1` per unit, so a minimum-cost circulation
is a circulation of maximum total flow value (`circValue`). -/
def residualArcs (G : Net) (x : Array ℤ) : StateM Cost (List ResArc) := do
  let mut arcs : Array ResArc := #[]
  for j in List.range G.cap.size do
    tick 1
    let xj := x.getD j 0
    let uj := G.cap.getD j 0
    if ← zlt xj uj then
      arcs := arcs.push ⟨G.tl.getD j 0, G.hd.getD j 0, -1, j, true⟩
    if ← zlt 0 xj then
      arcs := arcs.push ⟨G.hd.getD j 0, G.tl.getD j 0, 1, j, false⟩
  pure arcs.toList

end FlowAllocationGames.UnitRanking


