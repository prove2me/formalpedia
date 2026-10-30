-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_IsCirculation
-- name    : FlowAllocationGames_UnitRanking_IsCirculation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:13:40.334353+00:00
-- url     : https://prove2.me/theorems/72063c46-df58-4d17-8c4e-28a01bbfbd4f
-- title:
--   Circulation in $G'$
-- statement:
--   An integral flow $x$ on $G'$ is a **circulation** when
--
--   1. $x_e \le c_e$ for every edge $e$ of $G$;
--   2. $x_{(s,v)} \le b_v$ for every node $v$;
--   3. flow is conserved at every node $v$ of $G$: $x_{(s,v)} + \sum_{e\in E^-(v)} x_e = \sum_{e\in E^+(v)} x_e + x_{(v,s)}$;
--   4. flow is conserved at $s$: $\sum_v x_{(v,s)} = \sum_v x_{(s,v)}$.
--
--   The edges $(v, s)$ have infinite capacity, so $x_{(v,s)}$ is unbounded.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §3.1, p. 17; proof of Theorem 9, p. 23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_outFlow
import Definitions.Def_FlowAllocationGames_UnitRanking_inFlow
import Definitions.Def_FlowAllocationGames_UnitRanking_Circ

namespace FlowAllocationGames.UnitRanking

/-- **Circulation in `G′`.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §3.1, p. 17
(the circulation network `G′`, Proposition 5) and the proof of Theorem 9, p. 23 ("For a moment,
assume this is a standard flow network without strategic flow allocation").

`IsCirculation Γ x` holds when `x` respects the capacities `c e` of the edges of `G` and `b v` of
the edges `(s, v)`, and flow is conserved at every node `v` of `G`
(`fromS v + inflow = outflow + toS v`) and at `s` (`Σ toS = Σ fromS`).

**Formalization Note.** The edges `(v, s)` have capacity `∞` (p. 17), so `toS` is not bounded. -/
def IsCirculation {n m : ℕ} (Γ : Game n m) (x : Circ n m) : Prop :=
  (∀ e, x.flow e ≤ Γ.c e) ∧
  (∀ v, x.fromS v ≤ Γ.b v) ∧
  (∀ v, x.fromS v + inFlow Γ x.flow v = outFlow Γ x.flow v + x.toS v) ∧
  ∑ v, x.toS v = ∑ v, x.fromS v

end FlowAllocationGames.UnitRanking


