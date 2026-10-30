-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_cplus
-- name    : FlowAllocationGames_UnitRanking_cplus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:05:18.460518+00:00
-- url     : https://prove2.me/theorems/b443e1e3-e327-48a7-b29a-7b560814d5c5
-- title:
--   Saturating output $c^+_v$
-- statement:
--   The **saturating output** of a node $v$ is the maximum amount of flow $v$ can send to other players, the weighted outdegree
--
--   $$
--   c^+_v = \sum_{e \in E^+(v)} c_e .
--   $$
--
--   It appears in the no-fraud constraint $\sum_{e\in E^+(v)} a_e(y) = \min\{c^+_v, y\}$.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, p. 9

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_outFlow

namespace FlowAllocationGames.UnitRanking

/-- **Saturating output of a node.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.1, p. 9:
"The saturating output c⁺v of a node v is the maximum amount of flow v can send to other players,
specified by the weighted outdegree c⁺v = Σ_{e∈E⁺(v)} ce."

`cplus Γ v = Σ_{e ∈ E⁺(v)} c e`. -/
def cplus {n m : ℕ} (Γ : Game n m) (v : Fin n) : ℕ := outFlow Γ Γ.c v

end FlowAllocationGames.UnitRanking


