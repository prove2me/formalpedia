-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_maxCirc
-- name    : FlowAllocationGames_UnitRanking_maxCirc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:31:56.034594+00:00
-- url     : https://prove2.me/theorems/a1f3fc98-c5e3-4185-a04c-212de034e8c8
-- title:
--   Computing an optimal circulation of $G'$
-- statement:
--   Builds $G'$, starts from the zero flow and runs minimum-mean-cycle cancelling with the iteration budget; then reads off the flow on the edges of $G$, on the edges $(v, s)$ and on the edges $(s, v)$. This computes the optimal integral circulation $f^*$ that the proof of Theorem 9 starts from, in strongly polynomial time.
--
--   This is part of the witness algorithm of the mission: the paper computes the optimal circulation $f^*$ by citing Tardos [45] and fixes no algorithm.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Circ
import Definitions.Def_FlowAllocationGames_UnitRanking_Cost
import Definitions.Def_FlowAllocationGames_UnitRanking_tick
import Definitions.Def_FlowAllocationGames_UnitRanking_bitSizeZ
import Definitions.Def_FlowAllocationGames_UnitRanking_buildNet
import Definitions.Def_FlowAllocationGames_UnitRanking_cancelLoop
import Definitions.Def_FlowAllocationGames_UnitRanking_maxCircFuel

namespace FlowAllocationGames.UnitRanking

/-- **Computing an optimal circulation of `G′`.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23: "f∗ can be computed in strongly polynomial time [45]. Since all edge capacities are
integral, we can assume all f∗e are integral."

Builds `G′`, starts from the zero flow and runs minimum-mean-cycle cancelling with budget
`maxCircFuel n m`; then reads the flow on the edges of `G`, on the edges `(v, s)` and on the edges
`(s, v)`, ticking once per entry.

**Formalization Note.** The paper cites Tardos [45] and fixes no algorithm; the witness algorithm
(minimum-mean-cycle cancelling of Goldberg and Tarjan, with Karp's minimum-mean-cycle algorithm)
is the mission's choice (Reading 5). All arithmetic on flow values is ticked (see `tick`). -/
def maxCirc {n m : ℕ} (Γ : Game n m) : StateM Cost (Circ n m) := do
  let G ← buildNet Γ
  let x ← cancelLoop G (maxCircFuel n m) (Array.replicate G.cap.size 0)
  for j in List.range x.size do
    tick (bitSizeZ (x.getD j 0))
  pure ⟨fun e => (x.getD e 0).toNat, fun v => (x.getD (m + v) 0).toNat,
    fun v => (x.getD (m + n + v) 0).toNat⟩

end FlowAllocationGames.UnitRanking


