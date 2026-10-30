-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_cancelLoop
-- name    : FlowAllocationGames_UnitRanking_cancelLoop
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:29:59.200785+00:00
-- url     : https://prove2.me/theorems/0bbe6b62-e38c-4514-8106-528d74908642
-- title:
--   Minimum-mean-cycle cancelling
-- statement:
--   Repeatedly looks for a negative residual cycle of minimum mean cost and cancels it, stopping when there is none or when the iteration budget is used up. This is the minimum-mean-cycle-cancelling algorithm of Goldberg and Tarjan, which ends at a minimum-cost circulation.
--
--   This is part of the witness algorithm of the mission: the paper computes the optimal circulation $f^*$ by citing Tardos [45] and fixes no algorithm.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23; Goldberg, Tarjan, J. ACM 36 (1989)

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Cost
import Definitions.Def_FlowAllocationGames_UnitRanking_tick
import Definitions.Def_FlowAllocationGames_UnitRanking_Net
import Definitions.Def_FlowAllocationGames_UnitRanking_minMeanCycle
import Definitions.Def_FlowAllocationGames_UnitRanking_cancelStep

namespace FlowAllocationGames.UnitRanking

/-- **Minimum-mean-cycle cancelling with fuel.**
Witness algorithm of the mission for "f∗ can be computed in strongly polynomial time [45]" in
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23. Goldberg, Tarjan, *Finding minimum-cost circulations by canceling negative cycles*,
J. ACM 36 (1989).

With `fuel + 1` steps left, ticks once, looks for a negative residual cycle of minimum mean cost,
and stops if there is none; otherwise it cancels the cycle and continues with `fuel` steps. With
no fuel left it stops. -/
def cancelLoop (G : Net) : ℕ → Array ℤ → StateM Cost (Array ℤ)
  | 0, x => pure x
  | fuel + 1, x => do
    tick 1
    match ← minMeanCycle G x with
    | none => pure x
    | some cyc => cancelLoop G fuel (← cancelStep G x cyc)

end FlowAllocationGames.UnitRanking


