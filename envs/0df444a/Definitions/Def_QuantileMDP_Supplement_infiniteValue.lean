-- Prove2me | Definitions.Def_QuantileMDP_Supplement_infiniteValue
-- name    : QuantileMDP_Supplement_infiniteValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:53:07.10679+00:00
-- url     : https://prove2.me/theorems/30d9e0dd-bd27-5d8c-813f-7d162fa93f96
-- title:
--   The infinite-horizon optimal value $v(s,\tau)=\max_{\pi\in\Pi}Q^\pi_\tau\big[\sum_{t\ge0}\gamma^t r_t\,\big|\,S_0=s\big]$ (13)
-- statement:
--   Let $M$ be a Markov decision process with finite state set $\mathcal S$, transition laws $P_t(\cdot\mid s,a)$, rewards $r_t(s,a,s')$ and admissible action sets, and let $\gamma$ be a discount factor. For a start state $s$ and a level $\tau$, the infinite-horizon optimal value is
--
--   $$
--   v(s,\tau)=\max_{\pi\in\Pi}Q^\pi_\tau\Bigl[\sum_{t=0}^{\infty}\gamma^t r_t(S_t,a_t,w_t)\Bigm| S_0=s\Bigr], \tag{13}
--   $$
--
--   where $\Pi$ is the set of admissible deterministic history-dependent policies, $Q_\tau$ is the $\tau$-quantile of Definition 1 (with $Q_0$ the essential infimum and $Q_1$ the essential supremum), and the state path $S_0=s,S_1,S_2,\dots$ evolves under $\pi$ with $a_t=\mu_t(S_0,\dots,S_t)$.
--
--   This is the objective of the infinite-horizon quantile MDP of §5.3; Theorem 6 computes it by value iteration and Theorem 7 describes a policy that attains it.
--
--   **Formalization Note** The maximum is the supremum in the extended reals $\overline{\mathbb R}$ over the admissible policies (Theorem 6, published as `QuantileMDP.theorem_6_stationary`, shows it is attained under the assumptions of §5.3). The path law is the Ionescu–Tulcea measure `trajectoryLaw M π s` on $\mathcal S^{\mathbb N}$, the step reward is $r_k(S_k,a_k,S_{k+1})$ (`stepReward`), and the discounted reward is the series $\sum_k\gamma^k r_k$. Section 5.3 assumes a stationary reward and $\gamma\in(0,1)$; the theorems using $v$ add those hypotheses, under which the rewards of a finite model are bounded and the series converges on every path.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §5.3, (13), p.23

import Mathlib
import Definitions.Def_QuantileMDP_quantile
import Definitions.Def_QuantileMDP_Model
import Definitions.Def_QuantileMDP_discountedPath
import Definitions.Def_QuantileMDP_trajectory

open MeasureTheory

namespace QuantileMDP.Supplement

/-- The infinite-horizon optimal value function (13):
`v(s, τ) = max_{π ∈ Π} Q^π_τ[∑_{t=0}^∞ γ^t r_t(S_t, a_t, w_t) | S_0 = s]`.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, §5.3, (13), p.23.

**Formalization Note** The supremum (in `EReal`) ranges over all admissible deterministic
history-dependent policies `π` (`Model.Admissible`). The state path from `S_0 = s` under `π` has the
law `trajectoryLaw M π s` (Ionescu–Tulcea), the step reward at time `k` is
`stepReward M π k w = r_k(w_k, μ_k(w_0, …, w_k), w_{k+1})`, and the discounted reward is the
series `∑' k, γ ^ k * stepReward M π k w`; its quantile is `quantile` (Definition 1 with the
footnote-1 endpoints) of its law. Section 5.3 assumes a stationary reward and `γ ∈ (0,1)`; the
theorems that use this value add those hypotheses, under which (finite `S` and `A`) the rewards are
bounded and the series converges absolutely for every path. The measurable-space instances on `S`
are those `trajectoryLaw` needs; for a finite `S` with measurable singletons every set is
measurable. -/
noncomputable def infiniteValue {S A : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (M : Model S A) (γ : ℝ) (s : S) (τ : ℝ) : EReal :=
  ⨆ (π : Policy S A) (_ : M.Admissible π),
    quantile ((trajectoryLaw M π s).map (fun w => ∑' k, γ ^ k * stepReward M π k w)) τ

end QuantileMDP.Supplement


