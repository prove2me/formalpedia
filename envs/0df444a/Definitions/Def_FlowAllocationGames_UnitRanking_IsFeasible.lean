-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_IsFeasible
-- name    : FlowAllocationGames_UnitRanking_IsFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:07:43.242056+00:00
-- url     : https://prove2.me/theorems/c10fdad0-e7c7-4e22-a6f5-f033e31a5f8c
-- title:
--   Feasible flow of a profile
-- statement:
--   For a strategy profile $a$, an integral flow $f = (f_e)_{e\in E}$ is **feasible** when every edge carries what its tail allocates to it at its total supply:
--
--   $$
--   f_{(v,w)} = a_{(v,w)}(f_v) \quad \text{for every edge } (v, w) \in E, \qquad f_v = b_v + \sum_{e\in E^-(v)} f_e .
--   $$
--
--   This is the fixed point constraint (4). A profile can have no feasible flow, one, or several.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, p. 10, eq. (4)

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_supply
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile

namespace FlowAllocationGames.UnitRanking

/-- **Feasible flow of a profile.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.1, p. 10:
"For a strategy profile a = (ae)e∈E, a flow is called feasible if for all edges (v, w) ∈ E it
holds f(v,w) = a(v,w)(fv). (fixed point constraint) (4)".

`IsFeasible Γ a f` holds when `f e = a e (supply Γ f (tail e))` for every edge `e`.

**Formalization Note.** Flows are integral (`Fin m → ℕ`), as in the unit-ranking model of §2.2,
p. 13 ("choose the strategies such that the feasible flows will be integral"). -/
def IsFeasible {n m : ℕ} (Γ : Game n m) (a : Profile m) (f : Fin m → ℕ) : Prop :=
  ∀ e, f e = a e (supply Γ f (Γ.tail e))

end FlowAllocationGames.UnitRanking


