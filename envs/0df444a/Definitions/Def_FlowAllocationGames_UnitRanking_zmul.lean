-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_zmul
-- name    : FlowAllocationGames_UnitRanking_zmul
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:20:14.979481+00:00
-- url     : https://prove2.me/theorems/0de01ee3-d316-4232-a09a-a30c795c6ede
-- title:
--   Ticked integer multiplication
-- statement:
--   The ticked multiplication of two integers $a, b$ charges $\operatorname{opCost}(a, b)$ and returns the exact integer $a \cdot b$. Every integer multiplication performed by the algorithms of the mission goes through this operation.
--
--   This is part of the cost model in which the mission reads "can be computed in polynomial time" in Theorem 9; the paper itself fixes no machine model.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, Theorem 9, pp. 22–23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Cost
import Definitions.Def_FlowAllocationGames_UnitRanking_tick
import Definitions.Def_FlowAllocationGames_UnitRanking_opCost

namespace FlowAllocationGames.UnitRanking

/-- **Ticked integer multiplication.**
Cost model of the mission for Theorem 9 of Bertschinger, Hoefer, Schmand, *Flow Allocation Games*,
arXiv:1908.01714v3, pp. 22–23.

`zmul a b` charges `opCost a b` and returns the exact product `a * b`. -/
def zmul (a b : ℤ) : StateM Cost ℤ := do
  tick (opCost a b)
  pure (a * b)

end FlowAllocationGames.UnitRanking


