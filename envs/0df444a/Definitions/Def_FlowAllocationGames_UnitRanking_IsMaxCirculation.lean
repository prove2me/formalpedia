-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_IsMaxCirculation
-- name    : FlowAllocationGames_UnitRanking_IsMaxCirculation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:14:40.581567+00:00
-- url     : https://prove2.me/theorems/c6fa9c7f-7446-453e-bdcb-1d45b370db22
-- title:
--   Optimal circulation in $G'$
-- statement:
--   A circulation $f^*$ in $G'$ is **optimal** when its total flow value is at least that of every circulation in $G'$. The paper computes such an $f^*$ and turns it into the clearing state of a strong equilibrium.
--
--   **Formalization Note** The maximum is taken over integral circulations. The paper takes a real optimum and then assumes it integral ("Since all edge capacities are integral, we can assume all $f^*_e$ are integral"); the proof compares $f^*$ only with clearing states of unit-ranking profiles, which are integral.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Circ
import Definitions.Def_FlowAllocationGames_UnitRanking_IsCirculation
import Definitions.Def_FlowAllocationGames_UnitRanking_circValue

namespace FlowAllocationGames.UnitRanking

/-- **Optimal circulation in `G′`.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23: "Consider an optimal circulation f∗ that maximizes the total flow value … Since all edge
capacities are integral, we can assume all f∗e are integral."

`IsMaxCirculation Γ x` holds when `x` is a circulation in `G′` whose total flow value is at least
that of every circulation in `G′`.

**Formalization Note.** Reading 4 of the mission: the maximum is over integral circulations. The
paper takes a real optimum and then assumes it integral; the proof compares `f∗` only with
clearing states of unit-ranking profiles, which are integral. -/
def IsMaxCirculation {n m : ℕ} (Γ : Game n m) (x : Circ n m) : Prop :=
  IsCirculation Γ x ∧ ∀ y : Circ n m, IsCirculation Γ y → circValue y ≤ circValue x

end FlowAllocationGames.UnitRanking


