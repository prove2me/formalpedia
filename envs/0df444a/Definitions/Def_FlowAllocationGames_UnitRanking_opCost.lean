-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_opCost
-- name    : FlowAllocationGames_UnitRanking_opCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:18:10.839011+00:00
-- url     : https://prove2.me/theorems/e5458020-6c9d-4412-9cba-446dd126988c
-- title:
--   Cost of one arithmetic operation
-- statement:
--   The cost charged for one arithmetic operation or comparison on integers $a, b$ is
--
--   $$
--   \operatorname{opCost}(a, b) = \bigl(\operatorname{bitSize}(a) + \operatorname{bitSize}(b) + 1\bigr)^2 .
--   $$
--
--   Up to a constant factor this bounds the bit complexity of schoolbook addition, subtraction, multiplication and comparison. A computation whose numbers grow exponentially is charged exponentially.
--
--   This is part of the cost model in which the mission reads "can be computed in polynomial time" in Theorem 9; the paper itself fixes no machine model.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, Theorem 9, pp. 22–23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_bitSizeZ

namespace FlowAllocationGames.UnitRanking

/-- **Cost of one arithmetic operation on integers.**
Cost model of the mission for Theorem 9 of Bertschinger, Hoefer, Schmand, *Flow Allocation Games*,
arXiv:1908.01714v3, pp. 22–23.

`opCost a b = (bitSizeZ a + bitSizeZ b + 1)²`. Up to a constant factor this bounds the bit
complexity of schoolbook addition, subtraction, multiplication and comparison of `a` and `b`.

**Formalization Note.** The cost grows with the size of the numbers, so a run whose numbers grow
exponentially is charged exponentially. -/
def opCost (a b : ℤ) : ℕ := (bitSizeZ a + bitSizeZ b + 1) ^ 2

end FlowAllocationGames.UnitRanking


