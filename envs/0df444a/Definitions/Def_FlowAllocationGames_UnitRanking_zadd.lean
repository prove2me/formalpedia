-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_zadd
-- name    : FlowAllocationGames_UnitRanking_zadd
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:18:58.127316+00:00
-- url     : https://prove2.me/theorems/bbfd8308-ea43-4bc8-a19d-68af7638b85c
-- title:
--   Ticked integer addition
-- statement:
--   The ticked addition of two integers $a, b$ charges $\operatorname{opCost}(a, b)$ and returns the exact integer $a + b$. Every integer addition performed by the algorithms of the mission goes through this operation.
--
--   This is part of the cost model in which the mission reads "can be computed in polynomial time" in Theorem 9; the paper itself fixes no machine model.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, Theorem 9, pp. 22–23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Cost
import Definitions.Def_FlowAllocationGames_UnitRanking_tick
import Definitions.Def_FlowAllocationGames_UnitRanking_opCost

namespace FlowAllocationGames.UnitRanking

/-- **Ticked integer addition.**
Cost model of the mission for Theorem 9 of Bertschinger, Hoefer, Schmand, *Flow Allocation Games*,
arXiv:1908.01714v3, pp. 22–23.

`zadd a b` charges `opCost a b` and returns the exact sum `a + b`. -/
def zadd (a b : ℤ) : StateM Cost ℤ := do
  tick (opCost a b)
  pure (a + b)

end FlowAllocationGames.UnitRanking


