-- Prove2me | Definitions.Def_LightTailBandit_pseudoRegret
-- name    : LightTailBandit_pseudoRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:01.746573+00:00
-- url     : https://prove2.me/theorems/f22cb87f-ab3a-4a9d-b741-9ac6cee820ff
-- title:
--   Optimal mean $\theta_*$, gaps $\Delta_k$, empirical regret $\hat R(T)$, pseudo regret $R(T)$ and genuine noise $N(T)$
-- statement:
--   For a mean vector $\theta\in\mathbb R^K$ and one sample path of noises $\epsilon_{t,k}$ and actions $a_t$ over the horizon $T$:
--
--   1. $\theta_*=\max\{\theta_1,\dots,\theta_K\}$ and $\Delta_k=\theta_*-\theta_k$;
--   2. the **empirical regret** is $\hat R(T)=\theta_*\,T-\sum_{t=1}^T(\theta_{a_t}+\epsilon_{t,a_t})$;
--   3. the **pseudo regret** is $R(T)=\sum_{k=1}^K n_k\Delta_k$, where $n_k$ is the number of pulls of arm $k$ in the $T$ rounds;
--   4. the **genuine noise** is $N(T)=\sum_{t=1}^T\epsilon_{t,a_t}$.
--
--   They satisfy $\hat R(T)=R(T)-N(T)$ (proved in the mission's verification file). The empirical regret is the quantity whose tail Theorem 5 controls; the pseudo regret is the one whose mean it controls.
--
--   **Formalization Note** $\theta_*$ is a supremum over the finite set of arms; all items assume $K\ge2$. Rounds are 0-based.
-- source:
--   Simchi-Levi, Zheng, Zhu, A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk for Stochastic Bandits, arXiv:2206.02969v6, §2, p.8

import Mathlib
import Definitions.Def_FoundationsRL_Bandits_pullCount
import Definitions.Def_LightTailBandit_reward

open FoundationsRL.Bandits

namespace LightTailBandit

/-- **The optimal mean `θ_* = max{θ_1, …, θ_K}`** (arXiv:2206.02969v6, §2, p.8).

**Formalization Note.** A supremum over the finite type `Fin K`; every item of the mission assumes
`K ≥ 2`, so it is attained. -/
noncomputable def θstar {K : ℕ} (θ : Fin K → ℝ) : ℝ := ⨆ k, θ k

/-- **The gap `Δ_k = θ_* − θ_k`** of arm `k` (arXiv:2206.02969v6, §2, p.8). -/
noncomputable def gap {K : ℕ} (θ : Fin K → ℝ) (k : Fin K) : ℝ := θstar θ - θ k

/-- **The empirical regret** `R̂(T) = θ_* · T − Σ_{t=1}^T (θ_{a_t} + ϵ_{t,a_t})`
(arXiv:2206.02969v6, §2, p.8), along one sample path (mean vector `θ`, noise row `e`, actions `h`).

**Formalization Note.** Lean rounds `0, …, T−1` are the paper's rounds `1, …, T`. -/
noncomputable def empiricalRegret {K : ℕ} (θ : Fin K → ℝ) (T : ℕ) (e : ℕ → Fin K → ℝ)
    (h : ℕ → Fin K) : ℝ :=
  θstar θ * T - ∑ t ∈ Finset.range T, reward θ e h t

/-- **The pseudo regret** `R(T) = Σ_{k=1}^K n_k Δ_k` (arXiv:2206.02969v6, §2, p.8), where
`n_k = pullCount h T k` is the number of pulls of arm `k` in rounds `0, …, T−1`. -/
noncomputable def pseudoRegret {K : ℕ} (θ : Fin K → ℝ) (T : ℕ) (h : ℕ → Fin K) : ℝ :=
  ∑ k, (pullCount h T k : ℝ) * gap θ k

/-- **The genuine noise** `N(T) = Σ_{t=1}^T ϵ_{t,a_t}` (arXiv:2206.02969v6, §2, p.8), along one
sample path (noise row `e`, actions `h`). -/
def genuineNoise {K : ℕ} (T : ℕ) (e : ℕ → Fin K → ℝ) (h : ℕ → Fin K) : ℝ :=
  ∑ t ∈ Finset.range T, e t (h t)

end LightTailBandit


