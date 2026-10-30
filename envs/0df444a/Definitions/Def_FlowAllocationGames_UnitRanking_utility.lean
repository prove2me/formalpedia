-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_utility
-- name    : FlowAllocationGames_UnitRanking_utility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:09:39.822408+00:00
-- url     : https://prove2.me/theorems/edd67da0-cc10-4198-82d3-a13c06a2861d
-- title:
--   Utility $u_v(a)$ of a player
-- statement:
--   The **utility** of player $v$ in profile $a$ is its outgoing flow in the clearing state $\hat f$ of $a$:
--
--   $$
--   u_v(a) = u_v(a, \hat f) = \sum_{e \in E^+(v)} \hat f_e .
--   $$
--
--   Every player wants to maximize the total flow it forwards.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, p. 13

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_outFlow
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile
import Definitions.Def_FlowAllocationGames_UnitRanking_clearing

namespace FlowAllocationGames.UnitRanking

/-- **Utility of a player.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.1, p. 13:
"The clearing state f̂ determines the utility of every player in a, i.e.,
uv(a) = uv(a, f̂) = Σ_{e∈E⁺(v)} f̂e."

`utility Γ a v` is the outgoing flow of `v` in the clearing state of `a`. -/
noncomputable def utility {n m : ℕ} (Γ : Game n m) (a : Profile m) (v : Fin n) : ℕ :=
  outFlow Γ (clearing Γ a) v

end FlowAllocationGames.UnitRanking


