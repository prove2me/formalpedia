-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_inputSize
-- name    : FlowAllocationGames_UnitRanking_inputSize
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:23:50.034029+00:00
-- url     : https://prove2.me/theorems/d89faad9-f06d-4f7e-beeb-b3efcca04683
-- title:
--   Input size of a game
-- statement:
--   The **input size** of a game with $n$ nodes and $m$ edges is
--
--   $$
--   \operatorname{inputSize}(\Gamma) = n + m + \sum_{v} \operatorname{bitSize}(b_v) + \sum_{e} \operatorname{bitSize}(c_e),
--   $$
--
--   the number of objects plus the binary lengths of all supplies and capacities. Polynomial bounds on running time and representation size are stated in it.
--
--   **Formalization Note** The endpoints of the edges take $O(m \log n)$ further bits, which is polynomial in $n + m$, so leaving them out changes no polynomial bound.
--
--   This is part of the cost model in which the mission reads "can be computed in polynomial time" in Theorem 9; the paper itself fixes no machine model.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, p. 9; Theorem 9, pp. 22–23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_bitSize

namespace FlowAllocationGames.UnitRanking

/-- **Size of the input of a game.**
Cost model of the mission for Theorem 9 of Bertschinger, Hoefer, Schmand, *Flow Allocation Games*,
arXiv:1908.01714v3, pp. 22–23; §2.1, p. 9: "all numbers in the input, i.e., all bv and ce, are
integer numbers in binary encoding."

`inputSize Γ = n + m + Σ_v bitSize (b v) + Σ_e bitSize (c e)`.

**Formalization Note.** The endpoints of the edges take `O(m log n)` further bits, which is
polynomial in `n + m`, so omitting them changes no polynomial bound. -/
def inputSize {n m : ℕ} (Γ : Game n m) : ℕ :=
  n + m + ∑ v, bitSize (Γ.b v) + ∑ e, bitSize (Γ.c e)

end FlowAllocationGames.UnitRanking


