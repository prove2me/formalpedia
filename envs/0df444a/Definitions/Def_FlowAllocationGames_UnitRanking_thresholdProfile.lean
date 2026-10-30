-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_thresholdProfile
-- name    : FlowAllocationGames_UnitRanking_thresholdProfile
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:16:07.013388+00:00
-- url     : https://prove2.me/theorems/a97a4234-3870-44f3-8efd-cddb1d03753c
-- title:
--   Profile of threshold-ranking strategies
-- statement:
--   Given threshold-ranking data, node $v$ first assigns $\tau_e$ units to every edge $e\in E^+(v)$, sequentially in the order $\pi_v$, and then assigns the remaining $c_e - \tau_e$ units to every edge, again in the order $\pi_v$. For the $i$-th edge $e = \pi_v(i)$ and supply $y$ this gives
--
--   $$
--   a_e(y) = \min\Bigl\{\tau_e, \max\bigl\{0, y - \textstyle\sum_{j<i}\tau_{\pi_v(j)}\bigr\}\Bigr\} + \min\Bigl\{c_e - \tau_e, \max\bigl\{0, y - T_v - \textstyle\sum_{j<i}(c_{\pi_v(j)} - \tau_{\pi_v(j)})\bigr\}\Bigr\},
--   $$
--
--   where $T_v = \sum_{e\in E^+(v)} \tau_e$. Threshold-ranking strategies are unit-ranking strategies with a representation of polynomial size.
--
--   **Formalization Note** The truncations $\max\{0,\cdot\}$ are natural-number subtraction; $c_e - \tau_e$ is exact for valid data.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile
import Definitions.Def_FlowAllocationGames_UnitRanking_ThresholdRanking

namespace FlowAllocationGames.UnitRanking

/-- **The profile of threshold-ranking strategies.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23: "node v first assigns τe particles to every edge e ∈ E⁺(v), sequentially in the order given
by πv. Then, it assigns the remaining ce − τe particles to every edge in the order given by πv.
That is, v first considers edge πv(1) and forwards the first τπv(1) particles to this edge. The
next τπv(2) particles are forwarded to edge πv(2) etc. until Σ_{j=1}^{|E⁺(v)|} τπv(j) particles are
sent to the edges (or v runs out of flow). Then, the remaining cπv(1) − τπv(1) particles are
forwarded to edge πv(1), then the next cπv(2) − τπv(2) particles to πv(2) etc."

For an edge `e` with tail `v`, let `outs` be the edges with tail `v` in the order of `ord`, let
`preT` be the sum of `τ` over the edges before `e` in `outs`, `T` the sum of `τ` over all of `outs`,
and `preR` the sum of `c − τ` over the edges before `e`. With supply `y`, edge `e` receives
`min(τ e, max(0, y − preT)) + min(c e − τ e, max(0, y − T − preR))`.

**Formalization Note.** `ℕ`'s truncated subtraction computes `max(0, ·)` in `y - preT` and
`y - T - preR`, as intended; `c e - τ e` is exact for valid data (`IsValidThreshold`). -/
def thresholdProfile {n m : ℕ} (Γ : Game n m) (R : ThresholdRanking m) : Profile m :=
  fun e y =>
    let outs := R.1.filter (fun x => decide (Γ.tail x = Γ.tail e))
    let i := outs.idxOf e
    let preT := ((outs.take i).map R.2).sum
    let T := (outs.map R.2).sum
    let preR := ((outs.take i).map fun x => Γ.c x - R.2 x).sum
    min (R.2 e) (y - preT) + min (Γ.c e - R.2 e) (y - T - preR)

end FlowAllocationGames.UnitRanking


