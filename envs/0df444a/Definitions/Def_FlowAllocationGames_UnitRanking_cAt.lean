-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_cAt
-- name    : FlowAllocationGames_UnitRanking_cAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:22:10.179171+00:00
-- url     : https://prove2.me/theorems/f47977bb-be9a-47db-ae84-aa17ae130297
-- title:
--   Reading capacity $c_e$ from the input
-- statement:
--   Reading the capacity $c_e$ of an edge $e$ from the input charges $\operatorname{bitSize}(c_e) + 1$ and returns it. Every access of the algorithms of the mission to this part of the input goes through this operation.
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

/-- **Reading a capacity from the input.**
Cost model of the mission for Theorem 9 of Bertschinger, Hoefer, Schmand, *Flow Allocation Games*,
arXiv:1908.01714v3, pp. 22–23 (input numbers in binary encoding, p. 9).

`cAt Γ e` charges `bitSize (c e) + 1` and returns the capacity `c e` as an integer. -/
def cAt {n m : ℕ} (Γ : Game n m) (e : Fin m) : StateM Cost ℤ := do
  tick (bitSize (Γ.c e) + 1)
  pure (Γ.c e)

end FlowAllocationGames.UnitRanking


