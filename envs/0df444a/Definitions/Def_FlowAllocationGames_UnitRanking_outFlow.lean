-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_outFlow
-- name    : FlowAllocationGames_UnitRanking_outFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:03:14.152186+00:00
-- url     : https://prove2.me/theorems/c84f2dae-9aec-4cdb-ae48-bd909dbf63af
-- title:
--   Outgoing flow of a node
-- statement:
--   For a flow $f = (f_e)_{e\in E}$ and a node $v$, the **outgoing flow** of $v$ is
--
--   $$
--   \sum_{e \in E^+(v)} f_e ,
--   $$
--
--   where $E^+(v) = \{(v, u) \in E\}$ is the set of edges leaving $v$. It is the utility of $v$ when $f$ is the clearing state.
--
--   **Formalization Note** A self-loop at $v$ belongs to both $E^+(v)$ and $E^-(v)$.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, pp. 9–10

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game

namespace FlowAllocationGames.UnitRanking

/-- **Outgoing flow of a node.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.1, pp. 9–10
(`E⁺(v) = {(v, u) ∈ E}`; the utility `uv(a, f) = Σ_{e∈E⁺(v)} fe`).

`outFlow Γ f v = Σ_{e ∈ E⁺(v)} f e`, the sum of `f` over the edges whose tail is `v`.

**Formalization Note.** A self-loop at `v` belongs to both `E⁺(v)` and `E⁻(v)`. -/
def outFlow {n m : ℕ} (Γ : Game n m) (f : Fin m → ℕ) (v : Fin n) : ℕ :=
  ∑ e ∈ Finset.univ.filter (fun e => Γ.tail e = v), f e

end FlowAllocationGames.UnitRanking


