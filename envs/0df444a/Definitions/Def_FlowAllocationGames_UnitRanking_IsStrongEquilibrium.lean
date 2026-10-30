-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_IsStrongEquilibrium
-- name    : FlowAllocationGames_UnitRanking_IsStrongEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:12:40.972962+00:00
-- url     : https://prove2.me/theorems/82e87111-1a0f-4810-a922-1c4fb011edd1
-- title:
--   Strong equilibrium of a unit-ranking game
-- statement:
--   A profile $a$ of unit-ranking strategies is a **strong equilibrium** when no coalition has a profitable deviation: there is no nonempty coalition $C \subseteq V$ and no unit-ranking strategies $a'_C = (a'_v)_{v\in C}$ such that
--
--   $$
--   u_v(a'_C, a_{-C}) > u_v(a) \qquad \text{for every } v \in C .
--   $$
--
--   Utilities are computed from the clearing states. A strong equilibrium is in particular a pure Nash equilibrium (coalitions of size one).
--
--   **Formalization Note** Coalitions are nonempty: for $C = \emptyset$ the condition "strictly better for every player in $C$" holds vacuously, so the literal definition would admit no strong equilibrium at all. Deviations range over the game's strategy space (unit-ranking strategies); the deviating strategies are given as a whole profile $a'$ of which only the entries of $C$ are used.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.3, pp. 14–15

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile
import Definitions.Def_FlowAllocationGames_UnitRanking_IsUnitRankingProfile
import Definitions.Def_FlowAllocationGames_UnitRanking_utility
import Definitions.Def_FlowAllocationGames_UnitRanking_deviate

namespace FlowAllocationGames.UnitRanking

/-- **Strong equilibrium of a unit-ranking game.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.3, pp. 14–15:
"A coalition C ⊆ V of nodes has a profitable deviation a′C = (a′v)v∈C if upon joint deviation of
C to a′C, the resulting utility in the new profile (a′C, a−C) is strictly better for every player
in C, i.e., uv(a′C, a−C) > uv(a) for every v ∈ C. … A strategy profile a is a strong equilibrium
if no coalition C ⊆ V has any profitable deviation."

`IsStrongEquilibrium Γ a` holds when `a` is a profile of unit-ranking strategies and no nonempty
coalition `C` has a unit-ranking deviation `a'` under which every member of `C` gets strictly
higher utility.

**Formalization Note.** Reading 3 of the mission: coalitions are nonempty. For `C = ∅` the
condition "strictly better for every player in C" holds vacuously, so without `C.Nonempty` no
profile would ever be a strong equilibrium. Deviations range over the strategy space of the game,
unit-ranking strategies (§4, unit-ranking games); `a'` is a whole profile, of which only the
entries of the players in `C` are used, and every family of unit-ranking strategies for `C`
extends to such a profile. Utilities are those of the clearing states (`utility`). -/
def IsStrongEquilibrium {n m : ℕ} (Γ : Game n m) (a : Profile m) : Prop :=
  IsUnitRankingProfile Γ a ∧
  ∀ C : Finset (Fin n), C.Nonempty → ∀ a' : Profile m, IsUnitRankingProfile Γ a' →
    ¬ ∀ v ∈ C, utility Γ a v < utility Γ (deviate Γ a C a') v

end FlowAllocationGames.UnitRanking


