-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_computeSE
-- name    : FlowAllocationGames_UnitRanking_computeSE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:33:27.293984+00:00
-- url     : https://prove2.me/theorems/baaa864e-2d5b-44bd-8629-6e7f967458e8
-- title:
--   Computing the optimal strong equilibrium
-- statement:
--   Computes the optimal circulation $f^*$ of $G'$ and returns the threshold-ranking data in which every player orders its outgoing edges by index and sets $\tau_e = f^*_e$. The corresponding profile of threshold-ranking strategies is the strong equilibrium $a^*$ of Theorem 9.
--
--   **Formalization Note** The paper lets every player choose "an arbitrary permutation"; the algorithm fixes the index order.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_ThresholdRanking
import Definitions.Def_FlowAllocationGames_UnitRanking_Cost
import Definitions.Def_FlowAllocationGames_UnitRanking_tick
import Definitions.Def_FlowAllocationGames_UnitRanking_bitSize
import Definitions.Def_FlowAllocationGames_UnitRanking_maxCirc

namespace FlowAllocationGames.UnitRanking

/-- **Computing the optimal strong equilibrium.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23: "We choose a∗ as follows. Every firm v chooses an arbitrary permutation πv over E⁺(v) and
sets τe = f∗e."

Computes `f∗ = maxCirc Γ` and returns the threshold-ranking data `(ord, τ)` with `ord` the edges in
index order `0, …, m − 1` and `τ e = f∗ e`, ticking once per threshold.

**Formalization Note.** The "arbitrary permutation" is fixed to the index order (Reading 5). The
profile is `thresholdProfile Γ (computeSE Γ)`. -/
def computeSE {n m : ℕ} (Γ : Game n m) : StateM Cost (ThresholdRanking m) := do
  let x ← maxCirc Γ
  for e in List.finRange m do
    tick (bitSize (x.flow e))
  pure (List.finRange m, x.flow)

end FlowAllocationGames.UnitRanking


