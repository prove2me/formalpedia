-- Prove2me | Definitions.Def_LightTailBandit_reward
-- name    : LightTailBandit_reward
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:27.335972+00:00
-- url     : https://prove2.me/theorems/51e39ead-abba-4bab-8f6b-4f7697524133
-- title:
--   The reward $r_{t,a_t}=\theta_{a_t}+\epsilon_{t,a_t}$ and the empirical mean $\hat\theta_{t,k}$
-- statement:
--   Along one sample path, with mean vector $\theta=(\theta_1,\dots,\theta_K)$, noise values $\epsilon_{t,k}$ and actions $a_t$:
--
--   1. the **reward** of round $t$ is $r_{t,a_t}=\theta_{a_t}+\epsilon_{t,a_t}$;
--   2. the **empirical mean** of arm $k$ before round $t$ is
--   $$
--   \hat\theta_{t-1,k}=\frac{1}{n_{t-1,k}}\sum_{s<t,\ a_s=k} r_{s,a_s},
--   $$
--   where $n_{t-1,k}$ is the number of pulls of arm $k$ before round $t$ (the published pull count `FoundationsRL_Bandits_pullCount`).
--
--   These are the estimates that UCB compares.
--
--   **Formalization Note** Rounds are 0-based. When arm $k$ has not been pulled, Lean's division gives $0$; neither algorithm of the mission reads the empirical mean of an unpulled arm.
-- source:
--   Simchi-Levi, Zheng, Zhu, A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk for Stochastic Bandits, arXiv:2206.02969v6, §2, p.8 (rewards) and §2.1, p.11 (empirical mean θ̂_{t,k})

import Mathlib
import Definitions.Def_FoundationsRL_Bandits_pullCount

open FoundationsRL.Bandits

namespace LightTailBandit

/-- **The reward of round `t`** (arXiv:2206.02969v6, §2, p.8: "`r_{t,a_t} = θ_{a_t} + ϵ_{t,a_t}`").

Along one sample path, with mean vector `θ`, noise row `e t k` and actions `h t`, the reward of
round `t` is `θ (h t) + e t (h t)`.

**Formalization Note.** Rounds are 0-based (Lean round `t` is the paper's round `t + 1`). The
random reward is `reward θ (fun t k => ε t k ω) (fun t => a t ω) t`. -/
def reward {K : ℕ} (θ : Fin K → ℝ) (e : ℕ → Fin K → ℝ) (h : ℕ → Fin K) (t : ℕ) : ℝ :=
  θ (h t) + e t (h t)

/-- **The empirical mean `θ̂_{t-1,k}` of arm `k` before round `t`** (arXiv:2206.02969v6, §2.1,
p.11: "Let `θ̂_{t,k}` be the empirical mean reward of arm `k` up to time `t`").

`empMean θ e h t k` is the average of the rewards of the rounds `s < t` in which arm `k` was
pulled, i.e. the sum of those rewards divided by the pull count `pullCount h t k`
(`n_{t,k}` of the paper, counting pulls strictly before Lean round `t`).

**Formalization Note.** Lean round `t` is the paper's round `t + 1`, so `empMean θ e h t k` is the
paper's `θ̂_{t,k}` evaluated before the paper's round `t + 1`, as Algorithm 2 uses it. When arm `k`
has not been pulled the value is `0/0 = 0`; the algorithms of this mission never read it there. -/
noncomputable def empMean {K : ℕ} (θ : Fin K → ℝ) (e : ℕ → Fin K → ℝ) (h : ℕ → Fin K) (t : ℕ)
    (k : Fin K) : ℝ :=
  (∑ s ∈ (Finset.range t).filter (fun s => h s = k), reward θ e h s) / (pullCount h t k : ℝ)

end LightTailBandit


