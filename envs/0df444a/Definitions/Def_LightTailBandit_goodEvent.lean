-- Prove2me | Definitions.Def_LightTailBandit_goodEvent
-- name    : LightTailBandit_goodEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:55.090337+00:00
-- url     : https://prove2.me/theorems/566f2dcc-8300-43e2-aff8-4db6b41b10e1
-- title:
--   The set $\mathcal A_0$, the event $S_k$, the noise of the first $n$ pulls, and the good event $G$
-- statement:
--   Fix an optimal arm $b$ (the paper's arm 1). Along one sample path:
--
--   1. $k\in\mathcal A_0$ when $k\ne b$ and $n_k\le1+T/K$ (App. p.17);
--   2. for successive elimination, $S_k$ is the event that arm $b$ is not eliminated before arm $k$: in every phase starting no later than round $T$ in which $b$ is no longer active, $k$ is not active either (App. p.19);
--   3. $\Sigma_k(n)=\sum_{m=1}^{n}\epsilon_{t_k(m),k}$ is the noise of the first $n$ pulls of arm $k$ within the horizon, where $t_k(m)$ is the round of the $m$-th pull;
--   4. the **good event** is $G=\{\theta_k\in\mathrm{CI}_{t,k}\ \forall(t,k)\}$: for every arm $k$ and every $1\le n\le T$ with $n\le n_k$,
--   $$
--   \frac{|\Sigma_k(n)|}{n}\le\mathrm{rad}(n),
--   $$
--   i.e. the mean of the first $n$ rewards of arm $k$ lies within $\mathrm{rad}(n)$ of $\theta_k$ (App. p.17).
--
--   These are the events on which the proof of Theorem 5 splits the regret.
--
--   **Formalization Note** $\Sigma_k(n)$ adds the noises of the rounds before $T$ in which arm $k$ is pulled with fewer than $n$ earlier pulls, so it equals the paper's sum whenever $n\le n_k$.
-- source:
--   Simchi-Levi, Zheng, Zhu, A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk for Stochastic Bandits, arXiv:2206.02969v6, Online Appendix, proof of Theorem 5, pp.17 and 19 (PDF pp.54, 56)

import Mathlib
import Definitions.Def_FoundationsRL_Bandits_pullCount
import Definitions.Def_LightTailBandit_rad
import Definitions.Def_LightTailBandit_IsSERun

open FoundationsRL.Bandits

namespace LightTailBandit

/-- **Membership in `A₀`** (arXiv:2206.02969v6, Online Appendix, p.17 (PDF p.54):
"`A₀ = {k ≠ 1 : n_k ≤ 1 + T/K}`", the arms pulled no more than `1 + T/K` times).

`inA0 T h b k` holds when `k ≠ b` and `n_k = pullCount h T k ≤ 1 + T/K` (real division). Here `b`
is an optimal arm, the paper's "arm 1". -/
def inA0 {K : ℕ} (T : ℕ) (h : ℕ → Fin K) (b k : Fin K) : Prop :=
  k ≠ b ∧ (pullCount h T k : ℝ) ≤ 1 + (T : ℝ) / K

/-- **The event `S_k`: arm `b` is not eliminated before arm `k`** (arXiv:2206.02969v6, Online
Appendix, p.19 (PDF p.56): "`S_k = {Arm 1 is not eliminated before arm k}`").

Along one sample path of successive elimination: for every phase `n` starting no later than
round `T`, if `b` is no longer active in phase `n` then neither is `k`.

**Formalization Note.** Phases starting after `T` are not part of the run and are excluded. -/
def bSurvives {K : ℕ} (σ η₁ η₂ : ℝ) (T : ℕ) (θ : Fin K → ℝ) (e : ℕ → Fin K → ℝ)
    (h : ℕ → Fin K) (b k : Fin K) : Prop :=
  ∀ n, start σ η₁ η₂ T θ e h n ≤ T →
    b ∉ active σ η₁ η₂ T θ e h n → k ∉ active σ η₁ η₂ T θ e h n

/-- **The noise of the first `n` pulls of arm `k` within the horizon**,
`Σ_{m ≤ n} ϵ_{t_k(m),k}` (arXiv:2206.02969v6, §2, p.8, and Online Appendix pp.1, 17–24).

`armSum T e h k n` adds `e t k` over the rounds `t < T` in which arm `k` is pulled for the first,
second, …, `n`-th time (rounds with `h t = k` and fewer than `n` earlier pulls of `k`). When arm
`k` is pulled at least `n` times before `T` this is the paper's `Σ_{m=1}^n ϵ_{t_k(m),k}`. -/
def armSum {K : ℕ} (T : ℕ) (e : ℕ → Fin K → ℝ) (h : ℕ → Fin K) (k : Fin K) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, if h t = k ∧ pullCount h t k < n then e t k else 0

/-- **The good event `G = {θ_k ∈ CI_{t,k}, ∀(t,k)}`** (arXiv:2206.02969v6, Online Appendix, p.17
(PDF p.54)), with confidence intervals of half-width `rad(n)` around the mean of the first `n`
rewards.

Along one sample path: for every arm `k` and every `1 ≤ n ≤ T` with `n ≤ pullCount h T k`,
`|Σ_{m ≤ n} ϵ_{t_k(m),k}| / n ≤ rad(n)`, i.e. the mean of the first `n` rewards of arm `k` lies
within `rad(n)` of `θ_k`. -/
def goodEvent {K : ℕ} (σ η₁ η₂ : ℝ) (T : ℕ) (e : ℕ → Fin K → ℝ) (h : ℕ → Fin K) : Prop :=
  ∀ k n, 1 ≤ n → n ≤ T → n ≤ pullCount h T k → |armSum T e h k n| / n ≤ rad σ η₁ η₂ T K n

end LightTailBandit


