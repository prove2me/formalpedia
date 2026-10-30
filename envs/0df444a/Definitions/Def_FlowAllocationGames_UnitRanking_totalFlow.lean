-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_totalFlow
-- name    : FlowAllocationGames_UnitRanking_totalFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:10:42.149325+00:00
-- url     : https://prove2.me/theorems/95a57c63-15f9-453e-9315-50370f04625a
-- title:
--   Total amount of flow $\mathrm{Flow}(a)$
-- statement:
--   The **total (amount of) flow** of a strategy profile $a$ is the sum of the clearing state over all edges:
--
--   $$
--   \mathrm{Flow}(a) = \sum_{e \in E} \hat f_e .
--   $$
--
--   It equals the utilitarian welfare $\sum_v u_v(a)$ (equation (8)), and it is the quality measure maximized by the strong equilibrium of Theorem 9.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.3, p. 16, eq. (8)

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile
import Definitions.Def_FlowAllocationGames_UnitRanking_clearing

namespace FlowAllocationGames.UnitRanking

/-- **Total amount of flow of a profile.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.3, p. 16, eq. (8):
"the total (amount of) flow for a strategy profile a is Flow(a) = Σ_{e∈E} f̂e".

`totalFlow Γ a = Σ_e clearing Γ a e`. -/
noncomputable def totalFlow {n m : ℕ} (Γ : Game n m) (a : Profile m) : ℕ :=
  ∑ e, clearing Γ a e

end FlowAllocationGames.UnitRanking


