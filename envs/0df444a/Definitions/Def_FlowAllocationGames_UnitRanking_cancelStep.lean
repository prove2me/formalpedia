-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_cancelStep
-- name    : FlowAllocationGames_UnitRanking_cancelStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:29:08.388282+00:00
-- url     : https://prove2.me/theorems/80728e1f-0f7c-4870-917b-9844dae12e37
-- title:
--   Cancelling a residual cycle
-- statement:
--   Given a residual cycle, computes the minimum residual capacity $\delta$ along it ($\mathrm{cap}_j - x_j$ on a forward arc, $x_j$ on a backward arc) and pushes $\delta$ units around it: the flow increases by $\delta$ on the edges of the forward arcs and decreases by $\delta$ on the edges of the backward arcs. Conservation is preserved and the result is again integral.
--
--   This is part of the witness algorithm of the mission: the paper computes the optimal circulation $f^*$ by citing Tardos [45] and fixes no algorithm.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Cost
import Definitions.Def_FlowAllocationGames_UnitRanking_tick
import Definitions.Def_FlowAllocationGames_UnitRanking_zadd
import Definitions.Def_FlowAllocationGames_UnitRanking_zsub
import Definitions.Def_FlowAllocationGames_UnitRanking_zlt
import Definitions.Def_FlowAllocationGames_UnitRanking_Net
import Definitions.Def_FlowAllocationGames_UnitRanking_ResArc

namespace FlowAllocationGames.UnitRanking

/-- **Cancelling a residual cycle.**
Witness algorithm of the mission for "f∗ can be computed in strongly polynomial time [45]" in
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23.

Computes `δ`, the minimum residual capacity along the cycle (`cap − x` for a forward arc, `x` for
a backward arc), and pushes `δ` units around it: `x` increases by `δ` on the edges of the forward
arcs and decreases by `δ` on the edges of the backward arcs. -/
def cancelStep (G : Net) (x : Array ℤ) (cyc : List ResArc) : StateM Cost (Array ℤ) := do
  let mut δ : Option ℤ := none
  for a in cyc do
    tick 1
    let r ← if a.fwd then zsub (G.cap.getD a.edge 0) (x.getD a.edge 0)
      else pure (x.getD a.edge 0)
    match δ with
    | none => δ := some r
    | some d =>
      if ← zlt r d then
        δ := some r
  let d := δ.getD 0
  let mut y := x
  for a in cyc do
    tick 1
    let xe := y.getD a.edge 0
    let v ← if a.fwd then zadd xe d else zsub xe d
    y := y.set! a.edge v
  pure y

end FlowAllocationGames.UnitRanking


