-- Prove2me | Definitions.Def_StochLinOpt_LowerBound_circleBandit
-- name    : StochLinOpt_LowerBound_circleBandit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:34:09.269119+00:00
-- url     : https://prove2.me/theorems/e41542e4-24d8-4206-b4d8-83e93f1c8ba6
-- title:
--   The circle bandit of Theorem 3 ($n=2$): decision set $S^1$, uniform prior on $S^1/2$, $\pm1$ costs, randomised algorithms, expected regret
-- statement:
--   This file sets up the lower-bound instance of Dani, Hayes and Kakade (Section 3.3, Theorem 3) in the case $n=2$, together with the Bayesian posterior-bias update used in Section 6.1.
--
--   1. **Decision set.** $D_2=S^1=\{x\in\mathbb R^2:\ x_1^2+x_2^2=1\}$, the unit circle.
--   2. **Optimal cost.** For a mean vector $\mu\in\mathbb R^2$, $\mu\cdot x^*=\min_{x\in D_2}\mu\cdot x$ (written as an infimum over the compact circle, which is attained). For $\|\mu\|=1/2$ it equals $-1/2$.
--   3. **Prior.** $\mu(\theta)=\tfrac12(\cos\theta,\sin\theta)$; with $\theta$ uniform on $[0,2\pi)$, $\mu(\theta)$ is uniform on the circle $D_2/2$ of radius $1/2$.
--   4. **Costs.** Each cost is $\ell_t\in\{-1,+1\}$. Given $\mu$ and the decision $x_t$, $\ell_t=+1$ with probability $(1+\mu\cdot x_t)/2$ and $\ell_t=-1$ otherwise, so its mean is $\mu\cdot x_t$; given the decision, it is independent of the past.
--   5. **Algorithms.** A randomised algorithm draws a seed $s$ once from a probability measure $\rho$ on a measurable space $S$, and on round $t+1$ plays a point $x_{t+1}=\pi_t(s;\ell_1,\dots,\ell_t)$ of the unit circle that depends only on the seed and the costs observed so far, measurably in $s$. Every randomised algorithm is of this form (draw all internal randomness up front).
--   6. **Expected regret.** For horizon $T$, the cumulative regret is $R_T=\sum_{t=1}^T(\mu\cdot x_t-\mu\cdot x^*)$, and
--   $$\mathbb E R=\int_S\frac1{2\pi}\int_0^{2\pi}\sum_{\ell\in\{\pm1\}^T}\Big(\prod_{t=1}^T\frac{1+\ell_t\,\mu(\theta)\cdot x_t}{2}\Big)\,R_T\;d\theta\,d\rho(s),$$
--   where $x_t$ is computed from $s$ and $\ell_1,\dots,\ell_{t-1}$. This is exactly the expectation of $R_T$ under the joint law of seed, prior and costs, i.e. $\mathbb E_\mu\,\mathbb E(R\mid\mu)$.
--   7. **Posterior-bias update.** For two candidate means $\mu_1,\mu_2$, if the posterior probability of $\mu=\mu_1$ is $p$ and round $t$ plays $x$ and observes $\ell$, Bayes' rule gives the new bias
--   $$b'=\frac{p(1+\ell\,\mu_1\cdot x)-(1-p)(1+\ell\,\mu_2\cdot x)}{p(1+\ell\,\mu_1\cdot x)+(1-p)(1+\ell\,\mu_2\cdot x)}=\Pr(\mu=\mu_1\mid\mathcal H_{t+1})-\Pr(\mu=\mu_2\mid\mathcal H_{t+1}),$$
--   while the old bias is $b=2p-1$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Vectors are `Fin 2 → ℝ` with the dot product `⬝ᵥ`. Rounds are indexed from $0$ internally: the Lean index $t\in\{0,\dots,T-1\}$ is the paper's round $t+1$, and its decision sees the first $t$ costs. A cost $\pm1$ is stored as a Boolean (`true` for $+1$). The uniform prior is Lebesgue measure on $[0,2\pi)$ scaled by $1/(2\pi)$. The finite sum over the $2^T$ cost strings is the exact law of the costs for a finite horizon, so no infinite product of measures is needed. The algorithm's decisions need not depend only on the realised costs through a fixed horizon; a horizon-aware algorithm is covered because theorems quantify over every algorithm for each $T$.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 3, Section 2 (regret R_T); PDF p. 6, Section 3.3 (D_n, costs in {−1,+1} with mean µ·x, Theorem 3's prior µ uniform on D_n/n, n = 2); PDF p. 11, Section 6.1 (bias b_t and its Bayes update)

import Mathlib

open MeasureTheory Matrix

namespace StochLinOpt.LowerBound

/-- The decision set of the lower bound for `n = 2`: the unit circle
`D₂ = S¹ = {x ∈ ℝ² : x₁² + x₂² = 1}`. -/
def unitCircle : Set (Fin 2 → ℝ) := {x | x ⬝ᵥ x = 1}

/-- The optimal expected cost `μ · x* = min_{x ∈ D₂} μ · x` of the mean vector `μ`.
The image is nonempty and bounded (`|μ · x| ≤ ‖μ‖` on the circle), so the infimum is attained. -/
noncomputable def optCost (μ : Fin 2 → ℝ) : ℝ :=
  sInf ((fun x => μ ⬝ᵥ x) '' unitCircle)

/-- The point `μ(θ) = ½ (cos θ, sin θ)` of the circle `D₂ / 2` of radius `1/2`. With `θ` uniform
on `[0, 2π)`, `μ(θ)` is uniform on `D₂ / 2`. -/
noncomputable def meanVec (θ : ℝ) : Fin 2 → ℝ :=
  ![Real.cos θ / 2, Real.sin θ / 2]

/-- The cost value `ℓ ∈ {−1, +1}` encoded by a Boolean: `true ↦ +1`, `false ↦ −1`. -/
def signVal (b : Bool) : ℝ := if b then 1 else -1

/-- A (possibly randomised) algorithm for the circle bandit. All internal randomness is a seed
`s : S`, drawn once from a probability measure on `S`. Before round `t + 1` (0-based index `t`)
the algorithm has observed the `t` costs `ℓ₁, …, ℓ_t ∈ {±1}` (encoded as `Fin t → Bool`) and plays
`play t s (ℓ₁, …, ℓ_t)`, a point of the unit circle, measurable in the seed. -/
structure RandomizedPolicy (S : Type*) [MeasurableSpace S] where
  /-- The decision `x_{t+1}` as a function of the seed and the observed costs `ℓ₁, …, ℓ_t`. -/
  play : (t : ℕ) → S → (Fin t → Bool) → Fin 2 → ℝ
  /-- Every decision lies on the unit circle `D₂`. -/
  play_mem : ∀ t s h, play t s h ∈ unitCircle
  /-- Every decision is a measurable function of the seed. -/
  measurable_play : ∀ t h, Measurable fun s => play t s h

/-- The decision on the 0-based round `t < T` (the paper's round `t + 1`) when the seed is `s` and
the full cost string of the horizon is `ℓ`: it depends only on `ℓ` restricted to rounds `< t`. -/
def RandomizedPolicy.decisionAt {S : Type*} [MeasurableSpace S] (π : RandomizedPolicy S)
    (T : ℕ) (s : S) (ℓ : Fin T → Bool) (t : Fin T) : Fin 2 → ℝ :=
  π.play t s (fun i => ℓ (Fin.castLE t.isLt.le i))

/-- Probability of the cost string `ℓ ∈ {±1}^T` given the mean `μ` and the seed `s`: on each round
the cost is `+1` with probability `(1 + μ · x_t)/2` and `−1` otherwise (mean `μ · x_t`),
independently of the past given the decision. -/
noncomputable def costStringProb {S : Type*} [MeasurableSpace S] (π : RandomizedPolicy S)
    (T : ℕ) (s : S) (μ : Fin 2 → ℝ) (ℓ : Fin T → Bool) : ℝ :=
  ∏ t : Fin T, (1 + signVal (ℓ t) * (μ ⬝ᵥ π.decisionAt T s ℓ t)) / 2

/-- The cumulative regret `R_T = ∑_{t=1}^T (μ · x_t − μ · x*)` along the cost string `ℓ`. -/
noncomputable def cumulativeRegret {S : Type*} [MeasurableSpace S] (π : RandomizedPolicy S)
    (T : ℕ) (s : S) (μ : Fin 2 → ℝ) (ℓ : Fin T → Bool) : ℝ :=
  ∑ t : Fin T, (μ ⬝ᵥ π.decisionAt T s ℓ t - optCost μ)

/-- `E(R_T | μ, s)`: the expected cumulative regret over the observed costs, for a fixed mean `μ`
and a fixed seed `s`. -/
noncomputable def condExpectedRegret {S : Type*} [MeasurableSpace S] (π : RandomizedPolicy S)
    (T : ℕ) (s : S) (μ : Fin 2 → ℝ) : ℝ :=
  ∑ ℓ : Fin T → Bool, costStringProb π T s μ ℓ * cumulativeRegret π T s μ ℓ

/-- The Bayesian expected regret `E R = E_μ E(R | μ)` of Theorem 3 (`n = 2`): the seed `s ∼ ρ`,
the mean `μ = μ(θ)` with `θ` uniform on `[0, 2π)` (so `μ` is uniform on `D₂ / 2`), and the costs
drawn as in `costStringProb`. -/
noncomputable def expectedRegret {S : Type*} [MeasurableSpace S] (ρ : Measure S)
    (π : RandomizedPolicy S) (T : ℕ) : ℝ :=
  ∫ s, (2 * Real.pi)⁻¹ *
    (∫ θ in Set.Ico 0 (2 * Real.pi), condExpectedRegret π T s (meanVec θ)) ∂ρ

/-- The posterior bias after one observation. If before round `t` the posterior probability of
`μ = μ₁` (against `μ = μ₂`) is `p`, and on round `t` the decision is `x` and the observed cost is
`ℓ ∈ {±1}`, then Bayes' rule (likelihood of `ℓ` under `μᵢ` is `(1 + ℓ μᵢ · x)/2`) gives
`b_{t+1} = Pr(μ = μ₁ | H_{t+1}) − Pr(μ = μ₂ | H_{t+1})`, which is this expression. -/
noncomputable def biasUpdate (μ₁ μ₂ x : Fin 2 → ℝ) (p ℓ : ℝ) : ℝ :=
  (p * (1 + ℓ * (μ₁ ⬝ᵥ x)) - (1 - p) * (1 + ℓ * (μ₂ ⬝ᵥ x))) /
    (p * (1 + ℓ * (μ₁ ⬝ᵥ x)) + (1 - p) * (1 + ℓ * (μ₂ ⬝ᵥ x)))

end StochLinOpt.LowerBound


