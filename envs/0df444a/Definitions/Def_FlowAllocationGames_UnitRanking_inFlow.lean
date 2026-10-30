-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_inFlow
-- name    : FlowAllocationGames_UnitRanking_inFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:03:57.897913+00:00
-- url     : https://prove2.me/theorems/3acb7936-014d-4c1f-a012-08441c899eb2
-- title:
--   Incoming flow of a node
-- statement:
--   For a flow $f = (f_e)_{e\in E}$ and a node $v$, the **incoming flow** of $v$ is
--
--   $$
--   \sum_{e \in E^-(v)} f_e ,
--   $$
--
--   where $E^-(v) = \{(u, v) \in E\}$ is the set of edges entering $v$.
--
--   **Formalization Note** A self-loop at $v$ belongs to both $E^+(v)$ and $E^-(v)$.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, pp. 9–10

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game

namespace FlowAllocationGames.UnitRanking

/-- **Incoming flow of a node.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.1, pp. 9–10
(`E⁻(v) = {(u, v) ∈ E}`).

`inFlow Γ f v = Σ_{e ∈ E⁻(v)} f e`, the sum of `f` over the edges whose head is `v`.

**Formalization Note.** A self-loop at `v` belongs to both `E⁺(v)` and `E⁻(v)`. -/
def inFlow {n m : ℕ} (Γ : Game n m) (f : Fin m → ℕ) (v : Fin n) : ℕ :=
  ∑ e ∈ Finset.univ.filter (fun e => Γ.head e = v), f e

end FlowAllocationGames.UnitRanking


