-- Prove2me | Definitions.Def_TSTutorial_KnownStandard_Setting
-- name    : TSTutorial_KnownStandard_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:07.509581+00:00
-- url     : https://prove2.me/theorems/95bf36ec-5066-4af7-a477-72094e8f7333
-- title:
--   Example 8.1 and (4.2), pp. 19, 71, 79 — the known-standard problem, its Bayes posterior, stationary deterministic strategies and expected regret
-- statement:
--   This file sets up **Example 8.1 (A Known Standard)** of Russo, Van Roy, Kazerouni, Osband and Wen, *A Tutorial on Thompson Sampling* (p. 79).
--
--   **The problem.** There are two actions $\mathcal X=\{1,2\}$ and a binary parameter $\theta\in\{0,1\}$ with prior $\theta\sim\mathrm{Bernoulli}(p_0)$, i.e. $\mathbb P(\theta=1)=p_0$. Rewards are binary. Action $1$ pays $\mathrm{Bernoulli}(1/2)$ whatever $\theta$ is (the *known standard*); action $2$ pays $\mathrm{Bernoulli}(3/4)$ if $\theta=1$ and $\mathrm{Bernoulli}(1/4)$ if $\theta=0$. The mean reward $\mu(x,\theta)$ is the success probability of action $x$ under $\theta$, and the optimal mean is
--   $$\mu(x^*,\theta)=\max_{x\in\{1,2\}}\mu(x,\theta)=\begin{cases}3/4,&\theta=1,\\ 1/2,&\theta=0.\end{cases}$$
--
--   **Histories and the posterior.** A history $\mathbb H_t=((x_1,r_1),\dots,(x_t,r_t))$ records the action and the reward of each of the first $t$ periods. The posterior probability that $\theta=1$ given $\mathbb H_t$ is obtained from Bayes' rule (4.2) applied period by period:
--   $$p_t=\frac{p_0\,L_1(\mathbb H_t)}{p_0\,L_1(\mathbb H_t)+(1-p_0)\,L_0(\mathbb H_t)},\qquad L_\theta(\mathbb H_t)=\prod_{s=1}^{t}\mathbb P_\theta(r_s\mid x_s),$$
--   so that $p_0$ is the prior itself (empty history). The probabilities with which a strategy picks the actions do not depend on $\theta$ and cancel in Bayes' rule.
--
--   **Stationary deterministic strategies.** Such a strategy is one function $f$ from posterior probabilities to actions, used in every period: $x_t=f(p_{t-1})$.
--
--   **Expected regret.** Running $f$ from the prior $p_0$, a history $h$ of length $T$ has probability $\prod_{s=1}^T \mathbf 1[x_s=f(p_{s-1})]\,\mathbb P_\theta(r_s\mid x_s)$ given $\theta$, and the expected cumulative (Bayesian) regret (p. 71) is
--   $$\mathbb E[\mathrm{Regret}(T)]=\mathbb E\Big[\sum_{t=1}^T\big(\mu(x^*,\theta)-\mu(x_t,\theta)\big)\Big],$$
--   an expectation over $\theta\sim\mathrm{Bernoulli}(p_0)$ and the rewards, computed as a finite sum over $\theta$ and histories.
--
--   These objects are the whole model of Example 8.1; the theorems of this mission compute the regret of stationary deterministic strategies exactly.
--
--   **Formalization Note** The paper's action $1$ is `0 : Fin 2` and action $2$ is `1 : Fin 2`; $\theta=1$ is `true`; a reward $1$ is `true`. Lean period `s : Fin T` is the paper's period $s+1$, and `histPrefix h s` is $\mathbb H_{s}$, so `post p₀ (histPrefix h s)` is $p_{s}$, the posterior on which the action of paper period $s+1$ is based. `post` is defined by the closed form of iterated Bayes' rule; for $0<p_0\le 1$ its denominator is at least $p_0 4^{-t}>0$ (every reward probability is $1/2$, $1/4$ or $3/4$), so Lean's $x/0=0$ convention is never reached. A strategy is typed `ℝ → Fin 2`; its values outside $[0,1]$ are never used. `expRegret` is the finite sum $\sum_\theta \mathrm{prior}(\theta)\sum_h \mathbb P_\theta(h)\sum_{s}(\mu(x^*,\theta)-\mu(x_s,\theta))$.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), p. 19, (4.2); p. 71, §8.1.2 (expected cumulative regret); p. 79, §8.1.3, Example 8.1

import Mathlib

namespace TSTutorial.KnownStandard

/-- Success probability of action `a` under parameter `θ` in Example 8.1 (p. 79).
The paper's action 1 is `0 : Fin 2` (Bernoulli(1/2), known); the paper's action 2 is
`1 : Fin 2` (Bernoulli(3/4) if θ = 1, Bernoulli(1/4) if θ = 0). θ = 1 is `true`.
This is also the mean reward μ(a, θ). -/
noncomputable def succProb (θ : Bool) (a : Fin 2) : ℝ :=
  if a = 0 then 1 / 2 else if θ then 3 / 4 else 1 / 4

/-- Probability of observing reward `y` (`true` = 1, `false` = 0) from action `a` under `θ`. -/
noncomputable def rewardProb (θ : Bool) (a : Fin 2) (y : Bool) : ℝ :=
  if y then succProb θ a else 1 - succProb θ a

/-- The Bernoulli(p₀) prior on θ: ℙ(θ = 1) = p₀. -/
noncomputable def prior (p₀ : ℝ) (θ : Bool) : ℝ :=
  if θ then p₀ else 1 - p₀

/-- The optimal mean reward μ(x*, θ) = max_a μ(a, θ). -/
noncomputable def optMean (θ : Bool) : ℝ :=
  max (succProb θ 0) (succProb θ 1)

/-- A history of length `t`: the action and the reward of each of the first `t` periods
(ℍ_t). Lean period `s : Fin t` is the paper's period `s + 1`. -/
abbrev Hist (t : ℕ) : Type := Fin t → Fin 2 × Bool

/-- The prefix of length `s` of a history: ℍ_{s} inside ℍ_t. -/
def histPrefix {t : ℕ} (h : Hist t) (s : Fin t) : Hist s :=
  fun i => h (Fin.castLE s.isLt.le i)

/-- Likelihood of the observed rewards of `h` given θ (the policy's factors are omitted;
they do not depend on θ and cancel in Bayes' rule). -/
noncomputable def like {t : ℕ} (θ : Bool) (h : Hist t) : ℝ :=
  ∏ s : Fin t, rewardProb θ (h s).1 (h s).2

/-- The posterior p_t = ℙ(θ = 1 | ℍ_t = h) under the Bernoulli(p₀) prior, by Bayes' rule (4.2)
applied over the periods of `h`. -/
noncomputable def post {t : ℕ} (p₀ : ℝ) (h : Hist t) : ℝ :=
  p₀ * like true h / (p₀ * like true h + (1 - p₀) * like false h)

/-- A stationary deterministic strategy: the action in every period is `f` applied to the
current posterior probability that θ = 1, x_t = f(p_{t−1}); the same `f` in every period. -/
abbrev Strategy : Type := ℝ → Fin 2

/-- Indicator that the action of period `s` in `h` is the one the strategy `f` selects from
the posterior p_{s} computed from the prefix of `h` before period `s`. -/
noncomputable def act (f : Strategy) (p₀ : ℝ) {T : ℕ} (h : Hist T) (s : Fin T) : ℝ :=
  if (h s).1 = f (post p₀ (histPrefix h s)) then 1 else 0

/-- Probability of the length-`T` history `h` given θ when the strategy `f` is run from the
prior p₀. -/
noncomputable def lawGiven (f : Strategy) (p₀ : ℝ) (T : ℕ) (θ : Bool) (h : Hist T) : ℝ :=
  ∏ s : Fin T, act f p₀ h s * rewardProb θ (h s).1 (h s).2

/-- Expected cumulative regret 𝔼[Regret(T)] = 𝔼[Σ_{t=1}^T (μ(x*, θ) − μ(x_t, θ))] (p. 71) of
the strategy `f` under the prior Bernoulli(p₀), as a finite sum over θ and histories. -/
noncomputable def expRegret (f : Strategy) (p₀ : ℝ) (T : ℕ) : ℝ :=
  ∑ θ : Bool, prior p₀ θ *
    ∑ h : Hist T, lawGiven f p₀ T θ h * ∑ s : Fin T, (optMean θ - succProb θ (h s).1)

end TSTutorial.KnownStandard


