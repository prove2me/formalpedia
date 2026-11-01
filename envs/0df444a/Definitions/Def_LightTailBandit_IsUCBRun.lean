-- Prove2me | Definitions.Def_LightTailBandit_IsUCBRun
-- name    : LightTailBandit_IsUCBRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:59.966687+00:00
-- url     : https://prove2.me/theorems/ac775167-0f4c-47ef-a669-778012d14123
-- title:
--   Runs of UCB with the bonus (6) (Algorithm 2)
-- statement:
--   Along one sample path, actions $a_1,\dots,a_T$ are a **run of UCB with the bonus (6)** when, in every round $t\le T$:
--
--   1. if some arm has not been pulled before round $t$, then $a_t$ is such an arm;
--   2. otherwise $a_t$ maximizes the index $\hat\theta_{t-1,k}+\mathrm{rad}(n_{t-1,k})$ over all arms $k$, with ties broken in any way.
--
--   This is Algorithm 2 of the paper with the bonus of Theorem 5.
--
--   **Formalization Note** Clause 1 is the convention $\mathrm{rad}(0)=+\infty$ for an arm without samples, which the page leaves undefined. Rounds are 0-based, and $n_{t-1,k}$ counts pulls before the round. Any tie-breaking rule, deterministic or randomized, gives runs of this predicate; the verification file proves that a run exists for every noise path.
-- source:
--   Simchi-Levi, Zheng, Zhu, A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk for Stochastic Bandits, arXiv:2206.02969v6, Algorithm 2, p.11, with rad from (6), p.19

import Mathlib
import Definitions.Def_FoundationsRL_Bandits_pullCount
import Definitions.Def_LightTailBandit_reward
import Definitions.Def_LightTailBandit_rad

open FoundationsRL.Bandits

namespace LightTailBandit

/-- **A run of UCB with the bonus (6)** (arXiv:2206.02969v6, Algorithm 2, p.11, with `rad` of
(6), p.19): "Pull the arm with the highest UCB (randomly select one if a tie happens):
`argmax_k θ̂_{t−1,k} + rad(n_{t−1,k})`."

Along one sample path (mean vector `θ`, noise row `e`, actions `h`), the actions are a run of UCB
with horizon `T` when, for every round `t < T`:
1. if some arm has not been pulled before round `t`, then `h t` is an arm not pulled before `t`;
2. if every arm has been pulled before round `t`, then `h t` maximizes the index
   `empMean θ e h t k + rad σ η₁ η₂ T K (pullCount h t k)` over all arms `k`.

**Formalization Note.** Rounds are 0-based; `pullCount h t k` counts pulls in rounds `s < t`
(the paper's `n_{t−1,k}` at its round `t`). Clause 1 is the convention `rad(0) = +∞` for an arm
with no sample, which the page leaves undefined. Ties (in either clause) may be broken in any
way, deterministic or randomized, so the predicate describes every run of the algorithm. -/
def IsUCBRun {K : ℕ} (σ η₁ η₂ : ℝ) (T : ℕ) (θ : Fin K → ℝ) (e : ℕ → Fin K → ℝ)
    (h : ℕ → Fin K) : Prop :=
  ∀ t < T,
    ((∃ k, pullCount h t k = 0) → pullCount h t (h t) = 0) ∧
    ((∀ k, pullCount h t k ≠ 0) → ∀ k,
      empMean θ e h t k + rad σ η₁ η₂ T K (pullCount h t k) ≤
        empMean θ e h t (h t) + rad σ η₁ η₂ T K (pullCount h t (h t)))

end LightTailBandit


