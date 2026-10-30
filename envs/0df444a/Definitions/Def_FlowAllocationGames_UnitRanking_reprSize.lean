-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_reprSize
-- name    : FlowAllocationGames_UnitRanking_reprSize
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:24:22.459805+00:00
-- url     : https://prove2.me/theorems/b63f9d81-1bca-4eb3-8c90-5dcea5ee3fef
-- title:
--   Size of a threshold-ranking representation
-- statement:
--   The size of threshold-ranking data $(\mathrm{ord}, \tau)$ for a game with $m$ edges is
--
--   $$
--   |\mathrm{ord}| \cdot (\operatorname{size}(m) + 1) + \sum_{e} \operatorname{bitSize}(\tau_e),
--   $$
--
--   the bits of the list of edge indices plus the bits of the thresholds in binary. "The equilibrium profile can be represented in polynomial space" in Theorem 9 is the statement that this size is polynomial in the input size.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, Theorem 9, p. 23; proof of Theorem 9, p. 23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_ThresholdRanking
import Definitions.Def_FlowAllocationGames_UnitRanking_bitSize

namespace FlowAllocationGames.UnitRanking

/-- **Size of the representation of a threshold-ranking profile.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, Theorem 9, p. 23
("the equilibrium profile can be represented in polynomial space") and proof, p. 23
(threshold-ranking strategies "constitute a special class of unit-ranking strategies with compact
representation").

`reprSize (ord, τ) = length ord · (size m + 1) + Σ_e bitSize (τ e)`: the bits of the list of edge
indices plus the bits of the thresholds in binary. -/
def reprSize {m : ℕ} (R : ThresholdRanking m) : ℕ :=
  R.1.length * (Nat.size m + 1) + ∑ e, bitSize (R.2 e)

end FlowAllocationGames.UnitRanking


