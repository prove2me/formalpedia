-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_bAt
-- name    : FlowAllocationGames_UnitRanking_bAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:21:38.755327+00:00
-- url     : https://prove2.me/theorems/af546574-aa98-4c58-b88b-37bafac64374
-- title:
--   Reading supply $b_v$ from the input
-- statement:
--   Reading the supply $b_v$ of a node $v$ from the input charges $\operatorname{bitSize}(b_v) + 1$ and returns it. Every access of the algorithms of the mission to this part of the input goes through this operation.
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

/-- **Reading a supply from the input.**
Cost model of the mission for Theorem 9 of Bertschinger, Hoefer, Schmand, *Flow Allocation Games*,
arXiv:1908.01714v3, pp. 22–23 (input numbers in binary encoding, p. 9).

`bAt Γ v` charges `bitSize (b v) + 1` and returns the supply `b v` as an integer. -/
def bAt {n m : ℕ} (Γ : Game n m) (v : Fin n) : StateM Cost ℤ := do
  tick (bitSize (Γ.b v) + 1)
  pure (Γ.b v)

end FlowAllocationGames.UnitRanking


