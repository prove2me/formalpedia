-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_headAt
-- name    : FlowAllocationGames_UnitRanking_headAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:23:16.536443+00:00
-- url     : https://prove2.me/theorems/286873e9-36eb-4ca9-b771-9863243810a0
-- title:
--   Reading head from the input
-- statement:
--   Reading the head of an edge $e$ from the input charges $\operatorname{bitSize}(\mathrm{head}(e)) + 1$ and returns it. Every access of the algorithms of the mission to this part of the input goes through this operation.
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

/-- **Reading the head of an edge from the input.**
Cost model of the mission for Theorem 9 of Bertschinger, Hoefer, Schmand, *Flow Allocation Games*,
arXiv:1908.01714v3, pp. 22–23.

`headAt Γ e` charges `bitSize (head e) + 1` and returns the index of the head of `e`. -/
def headAt {n m : ℕ} (Γ : Game n m) (e : Fin m) : StateM Cost ℕ := do
  tick (bitSize (Γ.head e) + 1)
  pure (Γ.head e)

end FlowAllocationGames.UnitRanking


