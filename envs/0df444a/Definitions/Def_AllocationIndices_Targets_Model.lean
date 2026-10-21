-- Prove2me | Definitions.Def_AllocationIndices_Targets_Model
-- name    : AllocationIndices_Targets_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:55.868652+00:00
-- url     : https://prove2.me/theorems/46a2a257-9599-4668-b78b-1d10b3a8625e
-- title:
--   Calibration payoff R(λ, π), target cost M(φ, π, T), joint location–scale families and the sample mean/standard deviation update (§7.4)
-- statement:
--   The objects of §7.4 that the invariance theorems for joint location and scale parameters need, on top of the published sampling model of the series. A **sampling model** consists of a likelihood $f(\cdot \mid \theta)$, a family of priors $\pi(\cdot \mid p)$ on the parameter $\theta$ indexed by the parameters $p$ of a conjugate family, and the rule $p \mapsto p_x$ by which the parameters change when $x$ is the next value sampled. Its **reward process** moves from $p$ to $p_x$, $x$ drawn from the predictive distribution $f(\cdot \mid p) = \int f(\cdot \mid \theta)\,\pi(d\theta \mid p)$, and earns the predictive mean $r(p)$; its **target process** with target $T$ stops (reaches the completion state) as soon as a sampled value is $\ge T$, and earns the current probability of success. Rewards are discounted by $a^t$, $0 < a < 1$; $R_\tau$ is the expected discounted reward up to a stopping time $\tau$ and $\nu$ the Gittins index (2.6).
--
--   1. **Calibration payoff** (7.15). For a bandit process in state $x$ and a standard bandit process paying $\lambda$ per period,
--   $$R(\lambda, x) = \sup_{\tau} \Big\{ R_\tau(x) + \lambda (1 - a)^{-1} E(a^\tau \mid x) \Big\},$$
--   the supremum over all stopping times $\tau$ of the process's trajectory, $\tau = 0$ and $\tau = \infty$ included, with $a^\infty = 0$; $\tau$ is the time at which the standard bandit process is first selected (after which it is always selected).
--
--   2. **Target cost** (7.16). For the target process with target $T$ in state $p$ and a standard target process whose probability of reaching the target at each trial is a known $\varphi$,
--   $$M(\varphi, p, T) = \inf_\tau \Big\{ C_\tau(p, T) + \varphi^{-1} Q_\tau(p, T) \Big\},$$
--   where $C_\tau$ is the expected number of samples drawn from the target process before time $\tau$ or before the target is reached, whichever comes first, and $Q_\tau$ is the probability that $\tau$ is reached before the target. No discounting; $M$ takes values in $[0, \infty]$.
--
--   3. **Joint location and scale parameters** (p. 188). The likelihood $f(\cdot \mid \mu, \sigma)$ has joint location and scale parameters $\mu$, $\sigma$ if for $b > 0$ and real $c$ the distribution $f(\cdot \mid b\mu + c, b\sigma)$ is the image of $f(\cdot \mid \mu, \sigma)$ under $x \mapsto bx + c$.
--
--   4. **Prior families.** With $\sigma$ unknown, the prior on $(\mu, \sigma)$ has parameters $(\bar x, s, n)$, and $\bar x, s$ are joint location and scale parameters of the family (the intended content of (7.25)): the prior with parameters $(b\bar x + c, bs, n)$ is the image of the prior with parameters $(\bar x, s, n)$ under $(\mu, \sigma) \mapsto (b\mu + c, b\sigma)$. With $\sigma$ known (Corollary 7.14) the parameters are $(\bar x, n, \sigma)$ and the same image property holds with $(b\bar x + c, n, b\sigma)$.
--
--   5. **Update rules.** With $\sigma$ known, $(\bar x, n, \sigma) \mapsto \big((n\bar x + x)/(n+1),\ n + 1,\ \sigma\big)$ (Corollary 7.14). With $\sigma$ unknown, $(\bar x, s, n) \mapsto (\bar x', s', n + 1)$ by the rules of the sample mean and sample standard deviation $s = \big((n-1)^{-1}\sum_i (x_i - \bar x)^2\big)^{1/2}$ (Corollary 7.16):
--   $$\bar x' = \frac{n\bar x + x}{n + 1}, \qquad s' = \sqrt{\frac{(n-1)s^2 + n(x - \bar x)^2/(n+1)}{n}}.$$
--
--   **Formalization Note** `calibrationPayoff` is a real supremum over stopping times of the trajectory (`IsTrajStoppingTime`, the series' notion); the set is nonempty ($\tau = 0$) and, under the integrability hypothesis the theorems carry, bounded above. `targetCost` is an infimum in $[0, \infty]$; $C_\tau$ counts the times $t < \tau$ at which the target process has not yet reached the target, and $Q_\tau$ is the probability that $\tau$ is finite and the state at time $\tau$ is not the completion state. A "known" $\sigma$ is a coordinate of the state that the update never changes; the theorems require the prior to put all its mass on that value. The sample-standard-deviation rule is the book's only for $n > 1$, $s > 0$ (it divides by $n$ and needs $(n-1)s^2 > 0$); the theorems restrict to that domain.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §7.4 pp. 185–194 (Eqs. (7.10), (7.11), (7.15), (7.16), (7.25); location and scale parameters p. 188; Corollaries 7.14 and 7.16, p. 193)

import Definitions.Def_AllocationIndices_Sampling

open MeasureTheory ProbabilityTheory BanditAlgorithm

/-!
Gittins, Glazebrook and Weber, *Multi-armed Bandit Allocation Indices* (2nd ed., Wiley 2011),
§7.4 (pp. 185–194): the calibration payoff `R(λ, π)` of a sampling process against a standard
bandit process, the expected number of samples `M(φ, π, T)` of a target process against a
standard target process, joint location and scale parameters, and the two conjugate families of
Theorems 7.13 and 7.15 (σ known, state `(x̄, n, σ)`; σ unknown, state `(x̄, s, n)`).

The model is the published one (`Def_AllocationIndices_Sampling`): a `SamplingModel Θ P` is a
likelihood kernel `f(· | θ)`, a family of priors `π(· | p)` indexed by the parameters `p` of a
conjugate family, and the update of the parameters after one observation; `rewardChain`,
`rewardOf`, `targetChain`, `targetReward` are the reward and target processes on those parameters.

* `calibrationPayoff P r a λ x = R(λ, x) = sup_τ {R_τ(x) + λ (1 − a)⁻¹ E(a^τ | x)}` (7.15): the
  optimal payoff from the bandit process `(P, r)` in state `x` together with a standard bandit
  process paying `λ` per period, `τ` (any stopping time, `τ = 0` and `τ = ∞` included) being the
  time at which the standard bandit process is first selected; `a^∞ = 0`.
* `targetCost F T φ p = M(φ, p, T) = inf_τ {C_τ(p, T) + φ⁻¹ Q_τ(p, T)}` (7.16), undiscounted:
  `C_τ` is the expected number of samples drawn from the target process before time `τ` or before
  the target `T` is reached, whichever is first, and `Q_τ` the probability that `τ` is reached
  before the target. Valued in `[0, ∞]`.
* `HasJointLocationScale κ`: `μ` and `σ` are joint location and scale parameters of the likelihood
  `f(· | μ, σ)`: `f(· | bμ + c, bσ)` is the image of `f(· | μ, σ)` under `x ↦ bx + c` (`b > 0`).
* `PriorHasJointLocationScale η`: in the prior family with parameters `(x̄, s, n)`, `x̄` and `s` are
  joint location and scale parameters, in the sense of (7.25): the prior with parameters
  `(bx̄ + c, bs, n)` is the image of the prior with parameters `(x̄, s, n)` under
  `(μ, σ) ↦ (bμ + c, bσ)`.
* `PriorHasJointLocationScaleKnown η`: the same for the family with parameters `(x̄, n, σ)` of
  Corollary 7.14 (`σ` known), `(x̄, σ)` being the joint location and scale parameters.
* `knownScaleUpdate`: `(x̄, n, σ) ↦ ((n x̄ + x)/(n + 1), n + 1, σ)` (Corollary 7.14).
* `meanSdUpdate`: `(x̄, s, n) ↦ (x̄', s', n + 1)`, the rules by which the sample mean, the sample
  standard deviation `s = ((n − 1)⁻¹ Σ (x_i − x̄)²)^{1/2}` and the number of observations change
  when `x` is the next value sampled (Corollary 7.16):
  `x̄' = (n x̄ + x)/(n + 1)`, `n s'² = (n − 1) s² + n (x − x̄)²/(n + 1)`.
-/

open scoped ENNReal

namespace AllocationIndices.Targets

section Calibration

variable {S : Type*} [MeasurableSpace S]

/-- The calibration payoff `R(λ, x) = sup_τ {R_τ(x) + λ (1 − a)⁻¹ E(a^τ | x)}` (7.15): the
supremum over all stopping times `τ` (including `τ = 0` and `τ = ∞`) of the trajectory of the
bandit process `(P, r)` started in `x`. -/
noncomputable def calibrationPayoff (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (a lam : ℝ)
    (x : S) : ℝ :=
  ⨆ τ : {τ : (ℕ → S) → ℕ∞ // IsTrajStoppingTime τ},
    stoppedReward P r a τ.1 x + lam * (1 - a)⁻¹ * discountAtStop P a τ.1 x

end Calibration

section Target

variable {Θ Q : Type*} [MeasurableSpace Θ] [MeasurableSpace Q]

open Classical in
/-- `M(φ, p, T) = inf_τ {C_τ(p, T) + φ⁻¹ Q_τ(p, T)}` (7.16): the minimal expected number of
samples needed to reach the target `T`, given the target process in the state `p` and a standard
target process with known success probability `φ`, to which one switches for good at the stopping
time `τ`. `C_τ` counts the times `t < τ` at which the target process has not yet reached the target
(each is one sample); `Q_τ` is the probability that `τ` is finite and the target has not been
reached by time `τ`. Undiscounted. -/
noncomputable def targetCost (F : SamplingModel Θ Q) (T φ : ℝ) (p : Q) : ℝ≥0∞ :=
  ⨅ τ : {τ : (ℕ → Q ⊕ Unit) → ℕ∞ // IsTrajStoppingTime τ},
    (∫⁻ ω, ∑' t : ℕ, (if (t : ℕ∞) < τ.1 ω ∧ (ω t).isLeft then (1 : ℝ≥0∞) else 0)
        ∂markovChainMeasure (F.targetChain T) (Sum.inl p)) +
      ENNReal.ofReal φ⁻¹ *
        markovChainMeasure (F.targetChain T) (Sum.inl p)
          {ω | ∃ m : ℕ, τ.1 ω = (m : ℕ∞) ∧ (ω m).isLeft}

end Target

section Invariance

/-- `μ` and `σ` are **joint location and scale parameters** of the likelihood `f(· | μ, σ)`
(p. 188): for `b > 0` and real `c`, `f(· | bμ + c, bσ)` is the image of `f(· | μ, σ)` under
`x ↦ bx + c`. -/
def HasJointLocationScale (κ : Kernel (ℝ × ℝ) ℝ) : Prop :=
  ∀ μ σ b c : ℝ, 0 < b → κ (b * μ + c, b * σ) = (κ (μ, σ)).map (fun x ↦ b * x + c)

/-- In the prior family on `(μ, σ)` with parameters `(x̄, s, n)`, `x̄` and `s` are joint location
and scale parameters ((7.25), Corollary 7.16): the prior with parameters `(bx̄ + c, bs, n)` is the
image of the prior with parameters `(x̄, s, n)` under `(μ, σ) ↦ (bμ + c, bσ)`, for `b > 0`. -/
def PriorHasJointLocationScale (η : Kernel (ℝ × ℝ × ℝ) (ℝ × ℝ)) : Prop :=
  ∀ xb s n b c : ℝ, 0 < b →
    η (b * xb + c, b * s, n) = (η (xb, s, n)).map (fun θ ↦ (b * θ.1 + c, b * θ.2))

/-- In the prior family on `(μ, σ)` with parameters `(x̄, n, σ)` (`σ` known, Corollary 7.14), `x̄`
and `σ` are joint location and scale parameters: the prior with parameters `(bx̄ + c, n, bσ)` is
the image of the prior with parameters `(x̄, n, σ)` under `(μ, σ) ↦ (bμ + c, bσ)`, for `b > 0`. -/
def PriorHasJointLocationScaleKnown (η : Kernel (ℝ × ℝ × ℝ) (ℝ × ℝ)) : Prop :=
  ∀ xb n σ b c : ℝ, 0 < b →
    η (b * xb + c, n, b * σ) = (η (xb, n, σ)).map (fun θ ↦ (b * θ.1 + c, b * θ.2))

/-- The update of Corollary 7.14 (`σ` known): the parameters `(x̄, n, σ)` become
`((n x̄ + x)/(n + 1), n + 1, σ)` when `x` is the next value sampled. -/
noncomputable def knownScaleUpdate (p : ℝ × ℝ × ℝ) (x : ℝ) : ℝ × ℝ × ℝ :=
  ((p.2.1 * p.1 + x) / (p.2.1 + 1), p.2.1 + 1, p.2.2)

lemma measurable_knownScaleUpdate : Measurable (Function.uncurry knownScaleUpdate) := by
  unfold Function.uncurry knownScaleUpdate; fun_prop

/-- The update of Corollary 7.16: the parameters `(x̄, s, n)` change by the rules of the sample
mean, the sample standard deviation and the number of observations when `x` is the next value
sampled, `x̄' = (n x̄ + x)/(n + 1)`, `s' = √(((n − 1) s² + n (x − x̄)²/(n + 1))/n)`, `n' = n + 1`. -/
noncomputable def meanSdUpdate (p : ℝ × ℝ × ℝ) (x : ℝ) : ℝ × ℝ × ℝ :=
  ((p.2.2 * p.1 + x) / (p.2.2 + 1),
    Real.sqrt (((p.2.2 - 1) * p.2.1 ^ 2 + p.2.2 * (x - p.1) ^ 2 / (p.2.2 + 1)) / p.2.2),
    p.2.2 + 1)

lemma measurable_meanSdUpdate : Measurable (Function.uncurry meanSdUpdate) := by
  unfold Function.uncurry meanSdUpdate; fun_prop

end Invariance

end AllocationIndices.Targets


