-- Prove2me | Definitions.Def_OptimalBAI_LowerBound_ExpFamily
-- name    : OptimalBAI_LowerBound_ExpFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:45:53.226818+00:00
-- url     : https://prove2.me/theorems/819d3768-dcbc-43a9-b06c-f4f3bd6edd7c
-- title:
--   Canonical one-parameter exponential family and its bandit models
-- statement:
--   A **canonical one-parameter exponential family** is given by a reference measure $\xi$ on $\mathbb R$, a parameter set $\Theta \subset \mathbb R$ and a function $b : \Theta \to \mathbb R$, and consists of the laws $\nu_\theta$, $\theta \in \Theta$, with density
--
--   $$\frac{d\nu_\theta}{d\xi}(x) = \exp\big(\theta x - b(\theta)\big)$$
--
--   with respect to $\xi$. The data are required to satisfy:
--
--   1. $\Theta$ is a nonempty open interval;
--   2. every $\nu_\theta$, $\theta \in \Theta$, is a probability measure: $\int e^{\theta x - b(\theta)}\,d\xi(x) = 1$;
--   3. $b$ is twice continuously differentiable on $\Theta$;
--   4. $\ddot b(\theta) > 0$ for every $\theta \in \Theta$.
--
--   The mean of $\nu_\theta$ is $\dot b(\theta)$, and under 4 the mean map $\theta \mapsto \dot b(\theta)$ is injective, so each law of the family is determined by its mean.
--
--   A **bandit model** of the family with $K$ arms is a parameter vector $\theta = (\theta_1, \dots, \theta_K) \in \Theta^K$: arm $a$ returns rewards drawn from $\nu_{\theta_a}$, whose mean is $\mu_a = \dot b(\theta_a)$. Arm $a$ is **the (unique) optimal arm** of $\theta$, written $a = a^*(\theta)$, if $\dot b(\theta_a) > \dot b(\theta_i)$ for every other arm $i \ne a$.
--
--   Bernoulli laws ($\xi = \delta_0 + \delta_1$, $b(\theta) = \log(1 + e^\theta)$) and Gaussian laws with a known variance are the standard examples. The Kullback–Leibler divergence between two laws of the family, $d(\mu, \mu') = \mathrm{KL}(\nu_\theta, \nu_{\theta'}) = b(\theta') - b(\theta) - \dot b(\theta)(\theta' - \theta)$ when $\dot b(\theta) = \mu$, $\dot b(\theta') = \mu'$, is the divergence in which the paper's lower bound is expressed.
--
--   **Formalization Note** The paper asks only that $\Theta \subset \mathbb R$ and that $b$ be convex and twice differentiable. Conditions 1 and 4 are added: openness of $\Theta$ makes $\dot b$ and nearby alternative models meaningful, and $\ddot b > 0$ is what makes "the unique distribution with expectation $\mu$" well defined. Arms are indexed $0, \dots, K-1$ in Lean (the paper's arm $a$ is index $a - 1$). The bandit model is the platform's `BanditAlgorithm.StochasticBandit` with arm laws $\nu_{\theta_a}$; the identity "mean of $\nu_\theta$ $= \dot b(\theta)$" is a theorem, not part of the definition.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 3, §2 (definition of the canonical exponential family $\mathcal P$ and of exponential family bandit models) and §2.1 (unique optimal arm $a^*(\boldsymbol\mu)$)

import Mathlib
import Definitions.Def_StochasticBandit

open MeasureTheory

namespace OptimalBAI.LowerBound

/-- A canonical one-parameter exponential family (Garivier–Kaufmann, arXiv:1602.04589v2, p. 3, §2):
the laws `ν_θ` on `ℝ` with density `dν_θ/dξ (x) = exp(θ x - b(θ))` with respect to a reference
measure `ξ`, for `θ` in the parameter set `Θ`.

The paper asks that `b` be convex and twice differentiable. Two conditions are added and disclosed:
`Θ` is a nonempty open interval, and `b'' > 0` on `Θ` (strict convexity), which makes the mean map
`θ ↦ b'(θ)` injective, as the paper's "the unique distribution in `𝒫` with expectation `μ`"
requires. `isNormalized` says that every `ν_θ`, `θ ∈ Θ`, is a probability law. -/
structure ExpFamily where
  /-- The reference measure `ξ` on `ℝ`. -/
  ξ : Measure ℝ
  /-- The parameter set `Θ ⊆ ℝ`. -/
  Θ : Set ℝ
  /-- The log-partition function `b`. -/
  b : ℝ → ℝ
  isOpen_Θ : IsOpen Θ
  ordConnected_Θ : Θ.OrdConnected
  nonempty_Θ : Θ.Nonempty
  /-- Each `ν_θ`, `θ ∈ Θ`, has total mass one. -/
  isNormalized : ∀ θ ∈ Θ, ∫⁻ x, ENNReal.ofReal (Real.exp (θ * x - b θ)) ∂ξ = 1
  /-- `b` is twice (continuously) differentiable on `Θ`. -/
  contDiff : ContDiffOn ℝ 2 b Θ
  /-- `b` is strictly convex on `Θ`: `b''(θ) > 0`. -/
  deriv2_pos : ∀ θ ∈ Θ, 0 < deriv (deriv b) θ

namespace ExpFamily

/-- The law `ν_θ = exp(θ x - b(θ)) · ξ` of parameter `θ`. -/
noncomputable def arm (F : ExpFamily) (θ : ℝ) : Measure ℝ :=
  F.ξ.withDensity fun x => ENNReal.ofReal (Real.exp (θ * x - F.b θ))

/-- For `θ ∈ Θ`, `ν_θ` is a probability measure. -/
lemma isProbabilityMeasure_arm (F : ExpFamily) {θ : ℝ} (hθ : θ ∈ F.Θ) :
    IsProbabilityMeasure (F.arm θ) :=
  ⟨by rw [arm, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact F.isNormalized θ hθ⟩

/-- Arm `a` is the unique optimal arm of the exponential bandit model with parameters
`θ = (θ_1, …, θ_K)`: its mean `ḃ(θ_a)` is strictly larger than the mean `ḃ(θ_i)` of every other
arm `i ≠ a` (paper, p. 3: `μ_{a*(μ)} > max{μ_a : a ≠ a*(μ)}`). -/
def IsBestArm (F : ExpFamily) {K : ℕ} (θ : Fin K → F.Θ) (a : Fin K) : Prop :=
  ∀ i, i ≠ a → deriv F.b (θ i : ℝ) < deriv F.b (θ a : ℝ)

end ExpFamily

/-- The exponential-family bandit model with parameters `θ = (θ_1, …, θ_K) ∈ Θ^K`: arm `a`
(0-based) has reward law `ν_{θ_a}`; its mean is `ḃ(θ_a)`. -/
noncomputable def expFamilyBandit {K : ℕ} (F : ExpFamily) (θ : Fin K → F.Θ) :
    BanditAlgorithm.StochasticBandit K where
  P a := F.arm (θ a : ℝ)
  prob a := F.isProbabilityMeasure_arm (θ a).2

end OptimalBAI.LowerBound


