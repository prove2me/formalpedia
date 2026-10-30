-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_IsValidThreshold
-- name    : FlowAllocationGames_UnitRanking_IsValidThreshold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:15:34.655575+00:00
-- url     : https://prove2.me/theorems/311b0364-a614-467b-a4d9-f9fcaebdb87e
-- title:
--   Valid threshold-ranking data
-- statement:
--   Threshold-ranking data $(\mathrm{ord}, \tau)$ is **valid** when $\mathrm{ord}$ lists every edge exactly once and every threshold is at most the capacity, $\tau_e \le c_e$. Then $\pi_v$ is a permutation of $E^+(v)$ and the remaining amounts $c_e - \tau_e$ are nonnegative.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_ThresholdRanking

namespace FlowAllocationGames.UnitRanking

/-- **Valid threshold-ranking data.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23 (a permutation `πv` over `E⁺(v)` and thresholds `τe`; "it assigns the remaining ce − τe
particles", so `τe ≤ ce`).

`IsValidThreshold Γ (ord, τ)` holds when `ord` lists every edge exactly once and `τ e ≤ c e` for
every edge. -/
def IsValidThreshold {n m : ℕ} (Γ : Game n m) (R : ThresholdRanking m) : Prop :=
  R.1.Perm (List.finRange m) ∧ ∀ e, R.2 e ≤ Γ.c e

end FlowAllocationGames.UnitRanking


