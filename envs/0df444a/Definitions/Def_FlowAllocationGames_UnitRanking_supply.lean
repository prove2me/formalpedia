-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_supply
-- name    : FlowAllocationGames_UnitRanking_supply
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:04:31.846678+00:00
-- url     : https://prove2.me/theorems/8e5d0c23-e9e0-4139-b0ce-b82d1203217d
-- title:
--   Total supply of a node
-- statement:
--   Given a flow $f$, the **total supply** of a node $v$ is its fixed supply plus its incoming flow:
--
--   $$
--   f_v = b_v + \sum_{e \in E^-(v)} f_e .
--   $$
--
--   The strategy of $v$ allocates this amount to its outgoing edges.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, p. 10

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_inFlow

namespace FlowAllocationGames.UnitRanking

/-- **Total supply of a node under a flow.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.1, p. 10:
"Given some flow f, we slightly abuse notation and denote the total supply of v by
fv = bv + Σ_{e∈E⁻(v)} fe."

`supply Γ f v = b v + inFlow Γ f v`. -/
def supply {n m : ℕ} (Γ : Game n m) (f : Fin m → ℕ) (v : Fin n) : ℕ :=
  Γ.b v + inFlow Γ f v

end FlowAllocationGames.UnitRanking


