-- Prove2me | Definitions.Def_FlowAllocGames_StrongEq_Threshold
-- name    : FlowAllocGames_StrongEq_Threshold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:27.59364+00:00
-- url     : https://prove2.me/theorems/9bbbd52b-37f1-4841-8a24-150b081f13ce
-- title:
--   Proof of Theorem 9, p. 23 and p. 24 — threshold-ranking profiles and flow-monotone welfare functions
-- statement:
--   Two objects of §4.1 built on the model of flow allocation games.
--
--   **Threshold-ranking profiles.** Every node $v$ fixes a permutation $\pi_v$ of its outgoing edges $E^+(v)$ (encoded by a ranking $\mathrm{rank} : E \to \mathbb{N}$ that is injective on each $E^+(v)$, smaller rank first) and thresholds $\tau_e$ for $e \in E^+(v)$. With total supply $y$, node $v$ first forwards $\tau_{\pi_v(1)}$ units to $\pi_v(1)$, the next $\tau_{\pi_v(2)}$ units to $\pi_v(2)$ and so on, until $T_v = \sum_{e\in E^+(v)} \tau_e$ units are sent (or $v$ runs out of flow); then it forwards the remaining $c_{\pi_v(1)} - \tau_{\pi_v(1)}$ units to $\pi_v(1)$, the next $c_{\pi_v(2)} - \tau_{\pi_v(2)}$ to $\pi_v(2)$, and so on. In closed form, for $e \in E^+(v)$,
--
--   $$a_e(y) = \min\{\tau_e, (y - P_e)^+\} + \min\{c_e - \tau_e, (y - T_v - Q_e)^+\},$$
--
--   where $P_e$ is the sum of $\tau_{e'}$ and $Q_e$ the sum of $c_{e'} - \tau_{e'}$ over the edges $e' \in E^+(v)$ ranked before $e$, and $x^+ = \max\{0, x\}$.
--
--   **Flow-monotone welfare functions.** Let $\mathcal A$ be the set of unit-ranking profiles. A function $Q : \mathcal A \to \mathbb{R}$ is *flow-monotone* if for all $\mathbf a, \mathbf a' \in \mathcal A$ with clearing states $\hat{\mathbf f}, \hat{\mathbf f}'$, $\hat{\mathbf f} > \hat{\mathbf f}'$ implies $Q(\mathbf a) \ge Q(\mathbf a')$; here $\hat{\mathbf f} > \hat{\mathbf f}'$ means $\hat f_e \ge \hat f'_e$ for every edge and $\hat f_e > \hat f'_e$ for at least one.
--
--   Threshold-ranking profiles give the compact representation of the optimal strong equilibrium in the proof of Theorem 9; flow-monotone functions are the welfare functions covered by Corollary 12.
--
--   **Formalization Note.** Subtraction is in $\mathbb{N}$ and truncated at $0$, which is the page's "or $v$ runs out of flow"; $c_e - \tau_e$ is the page's residual capacity whenever $\tau_e \le c_e$. Injectivity of the ranking on each $E^+(v)$ is not part of the definition; it is a hypothesis of every statement that uses a threshold-ranking profile. $Q$ is typed on all profiles; flow-monotonicity only constrains its values on unit-ranking profiles, and the order $>$ is Mathlib's strict order on functions $E \to \mathbb{N}$, which is the paper's (p. 12).
-- source:
--   arXiv:1908.01714v3, proof of Theorem 9, p. 23 (threshold-ranking strategies); p. 24, definition before Corollary 12 (flow-monotone Q)

import Mathlib
import Definitions.Def_FlowAllocGames_StrongEq_Model

namespace FlowAllocGames.StrongEq

open Finset

namespace Game

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : Game V E)

/-- The threshold-ranking profile (arXiv:1908.01714v3, proof of Theorem 9, p. 23): node `v` orders
`E⁺(v)` by `rank` (smaller first; `π_v` is `rank` restricted to `E⁺(v)`) and uses thresholds `τ`.
Edge `e` first gets `min(τ_e, (y − P_e)⁺)`, with `P_e` the sum of the thresholds of the edges of
`E⁺(v)` ranked before `e`; then `min(c_e − τ_e, (y − T_v − Q_e)⁺)`, with `T_v = Σ_{E⁺(v)} τ` and
`Q_e` the sum of the residual capacities `c − τ` of the edges ranked before `e`. Natural-number
subtraction is truncated, which is the page's "or `v` runs out of flow". -/
def thresholdProfile (rank : E → ℕ) (τ : E → ℕ) : Profile E := fun e y =>
  min (τ e) (y - ∑ e' ∈ (G.outEdges (G.tail e)).filter (fun e' => rank e' < rank e), τ e') +
  min (G.c e - τ e) (y - ∑ e' ∈ G.outEdges (G.tail e), τ e' -
    ∑ e' ∈ (G.outEdges (G.tail e)).filter (fun e' => rank e' < rank e), (G.c e' - τ e'))

/-- A social welfare function `Q : 𝒜 → ℝ` is flow-monotone (arXiv:1908.01714v3, p. 24): for
unit-ranking profiles `a, a′` with clearing states `f̂, f̂′`, `f̂ > f̂′` (coordinatewise `≥` and
somewhere `>`) implies `Q(a) ≥ Q(a′)`. -/
def IsFlowMonotone (Q : Profile E → ℝ) : Prop :=
  ∀ a a' : Profile E, G.IsUnitRanking a → G.IsUnitRanking a' →
    G.clearingState a' < G.clearingState a → Q a' ≤ Q a

end Game

end FlowAllocGames.StrongEq


