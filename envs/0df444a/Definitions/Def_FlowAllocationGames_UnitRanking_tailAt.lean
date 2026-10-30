-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_tailAt
-- name    : FlowAllocationGames_UnitRanking_tailAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:22:47.450416+00:00
-- url     : https://prove2.me/theorems/ef52ea3a-bca7-4ccb-b68b-9df6c8392b7b
-- title:
--   Reading tail from the input
-- statement:
--   Reading the tail of an edge $e$ from the input charges $\operatorname{bitSize}(\mathrm{tail}(e)) + 1$ and returns it. Every access of the algorithms of the mission to this part of the input goes through this operation.
--
--   This is part of the cost model in which the mission reads "can be computed in polynomial time" in Theorem 9; the paper itself fixes no machine model.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, p. 9 (binary encoding); Theorem 9, pp. 22–23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Cost
import Definitions.Def_FlowAllocationGames_UnitRanking_tick
import Definitions.Def_FlowAllocationGames_UnitRanking_bitSize

namespace FlowAllocationGames.UnitRanking

/-- **Reading the tail of an edge from the input.**
Cost model of the mission for Theorem 9 of Bertschinger, Hoefer, Schmand, *Flow Allocation Games*,
arXiv:1908.01714v3, pp. 22–23.

`tailAt Γ e` charges `bitSize (tail e) + 1` and returns the index of the tail of `e`. -/
def tailAt {n m : ℕ} (Γ : Game n m) (e : Fin m) : StateM Cost ℕ := do
  tick (bitSize (Γ.tail e) + 1)
  pure (Γ.tail e)

end FlowAllocationGames.UnitRanking


