-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_IsUnitRankingProfile
-- name    : FlowAllocationGames_UnitRanking_IsUnitRankingProfile
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:06:56.117973+00:00
-- url     : https://prove2.me/theorems/580d0139-883a-49f1-930d-20c5f257be53
-- title:
--   Profile of unit-ranking strategies
-- statement:
--   A strategy profile $a$ consists of **unit-ranking strategies** when it consists of monotone strategies (constraints (1), (2), (5)) that also satisfy the **no-fraud constraint** (3): for every node $v$ and every integer supply $y \ge 0$,
--
--   $$
--   \sum_{e \in E^+(v)} a_e(y) = \min\{c^+_v, y\} .
--   $$
--
--   Every player forwards as much of its total supply as its outgoing capacities allow. With integral supplies and monotone allocations, the outputs of $v$ grow by single units, one edge at a time, until $c^+_v$; this is a ranking of the units of flow, the unit-ranking strategies of the paper. These are the strategy spaces of a unit-ranking game.
--
--   **Formalization Note** The paper describes unit-ranking strategies by rankings of particles (p. 14); the integral strategies with (1), (2), (3), (5) are exactly these. Constraint (2) follows from (3) and is kept so that the first part is the paper's notion of monotone strategies.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, p. 10, constraint (3); §2.2, pp. 13–14

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_cplus
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile
import Definitions.Def_FlowAllocationGames_UnitRanking_IsMonotoneProfile

namespace FlowAllocationGames.UnitRanking

/-- **Profile of unit-ranking strategies.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.1, p. 10,
constraint (3) `Σ_{e∈E⁺(v)} ae(y) = min{c⁺v, y}` (no-fraud; "We assume this property in the
strategies for simplicity"); §2.2, pp. 13–14 (unit-ranking strategies: integral strategies
`ae : N0 → N0`, a player "assigns the first particle of flow to the multi-edge πv(1), the second
particle to πv(2), etc.").

`IsUnitRankingProfile Γ a` holds when `a` is a profile of monotone strategies (1), (2), (5) that
also satisfies the no-fraud constraint (3) at every node and every integral supply `y`.

**Formalization Note.** Reading 2 of the mission: a unit-ranking strategy is an integral strategy
`ℕ → ℕ` with (1), (2), (3), (5). Under (3) and (5) the outputs of `v` increase by single units,
one edge at a time, until `c⁺v`, which is exactly a ranking of the units of p. 14. Constraint (2)
follows from (3) and is kept so that the first conjunct is p. 11's notion. -/
def IsUnitRankingProfile {n m : ℕ} (Γ : Game n m) (a : Profile m) : Prop :=
  IsMonotoneProfile Γ a ∧
  ∀ v y, ∑ e ∈ Finset.univ.filter (fun e => Γ.tail e = v), a e y = min (cplus Γ v) y

end FlowAllocationGames.UnitRanking


