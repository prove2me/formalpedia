-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_zlt
-- name    : FlowAllocationGames_UnitRanking_zlt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:20:59.158135+00:00
-- url     : https://prove2.me/theorems/8da58391-a85a-410f-8094-9418ab6dfaf4
-- title:
--   Ticked integer comparison
-- statement:
--   The ticked comparison of two integers $a, b$ charges $\operatorname{opCost}(a, b)$ and returns whether $a < b$. Every test on integer data made by the algorithms of the mission goes through this operation.
--
--   This is part of the cost model in which the mission reads "can be computed in polynomial time" in Theorem 9; the paper itself fixes no machine model.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, Theorem 9, pp. 22–23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Cost
import Definitions.Def_FlowAllocationGames_UnitRanking_tick
import Definitions.Def_FlowAllocationGames_UnitRanking_opCost

namespace FlowAllocationGames.UnitRanking

/-- **Ticked integer comparison `a < b`.**
Cost model of the mission for Theorem 9 of Bertschinger, Hoefer, Schmand, *Flow Allocation Games*,
arXiv:1908.01714v3, pp. 22–23.

`zlt a b` charges `opCost a b` and returns the truth value of `a < b` as a `Bool`. -/
def zlt (a b : ℤ) : StateM Cost Bool := do
  tick (opCost a b)
  pure (decide (a < b))

end FlowAllocationGames.UnitRanking


