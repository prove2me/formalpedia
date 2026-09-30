-- Prove2me | Definitions.Def_OptimalBAI_TrackStop_ExpFamily
-- name    : OptimalBAI_TrackStop_ExpFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:04:30.523162+00:00
-- url     : https://prove2.me/theorems/9c2230d9-d8eb-47a1-a630-7fb04321e569
-- title:
--   Canonical one-parameter exponential family, its bandit models and the class $\mathcal S$
-- statement:
--   A **canonical one-parameter exponential family** is a family of probability laws $(\nu_\theta)_{\theta\in\Theta}$ on $\mathbb R$ with densities
--   $$\frac{d\nu_\theta}{d\xi}(x)=\exp\big(\theta x-b(\theta)\big)$$
--   with respect to a reference measure $\xi$, where $\Theta\subset\mathbb R$ is the parameter set and $b$ is the log-partition function. It is recorded by the data $(\xi,\Theta,b)$ together with the requirements that $\Theta$ is a nonempty open interval, that every $\nu_\theta$ ($\theta\in\Theta$) has total mass one, that $b$ is twice continuously differentiable on $\Theta$, and that $\ddot b(\theta)>0$ on $\Theta$.
--
--   The law $\nu_\theta$ has mean $\dot b(\theta)$; the **mean space** is $\dot b(\Theta)$. For $\mu\in\dot b(\Theta)$, $\theta(\mu)$ denotes the unique $\theta\in\Theta$ with $\dot b(\theta)=\mu$, and the divergence on the mean space is
--   $$d(\mu,\mu')=b(\theta(\mu'))-b(\theta(\mu))-\mu\,\big(\theta(\mu')-\theta(\mu)\big),$$
--   which equals the Kullback–Leibler divergence $\mathrm{KL}(\nu^{\mu},\nu^{\mu'})$.
--
--   An **exponential family bandit model** with $K$ arms is a parameter vector $\theta=(\theta_1,\dots,\theta_K)\in\Theta^K$; arm $a$ yields rewards drawn from $\nu_{\theta_a}$, and its mean vector is $\boldsymbol\mu=(\dot b(\theta_1),\dots,\dot b(\theta_K))$. The class $\mathcal S$ consists of the models with a unique optimal arm: some arm $a$ has $\dot b(\theta_a)>\dot b(\theta_i)$ for every $i\ne a$. The set of bandit environments obtained from $\mathcal S$ is the class over which the alternative set $\mathrm{Alt}(\boldsymbol\mu)$ and the characteristic time $T^*(\boldsymbol\mu)$ are taken.
--
--   These objects are the standing model of the whole paper; every statement of the mission is about a bandit model in $\mathcal S$.
--
--   **Formalization Note** The paper only asks that $b$ be convex and twice differentiable and that $\Theta\subset\mathbb R$. Openness and connectedness of $\Theta$ and $\ddot b>0$ are added: strict convexity is what makes "the unique distribution with expectation $\mu$" well defined, and openness makes means of nearby models meaningful. Arms are indexed $0,\dots,K-1$. The parameter of a mean outside $\dot b(\Theta)$ is an unspecified value that no statement uses.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 3, §2 (exponential family, divergence d); p. 4 (class S)

import Mathlib
import Definitions.Def_BanditTrajectory

open MeasureTheory

namespace OptimalBAI.TrackStop

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

/-- The mean space `ḃ(Θ)`: the set of means `μ = ḃ(θ)` of the laws of the family. -/
def M (F : ExpFamily) : Set ℝ := deriv F.b '' F.Θ

/-- The natural parameter of mean `μ`: the `θ ∈ Θ` with `ḃ(θ) = μ` (unique for `μ ∈ ḃ(Θ)`, since
`ḃ` is strictly increasing on `Θ`; its value for `μ ∉ ḃ(Θ)` is immaterial and never used). -/
noncomputable def θof (F : ExpFamily) (μ : ℝ) : ℝ :=
  Function.invFunOn (deriv F.b) F.Θ μ

/-- The divergence `d(μ, μ') = KL(ν^μ, ν^{μ'}) = b(θ') - b(θ) - ḃ(θ)(θ' - θ)` on the mean space,
where `ḃ(θ) = μ` and `ḃ(θ') = μ'` (paper, p. 3). Only its values for `μ, μ' ∈ ḃ(Θ)` are meaningful;
there `ḃ(θ) = μ`, so the last term is written `μ (θ' - θ)`. -/
noncomputable def d (F : ExpFamily) (μ μ' : ℝ) : ℝ :=
  F.b (F.θof μ') - F.b (F.θof μ) - μ * (F.θof μ' - F.θof μ)

end ExpFamily

/-- The exponential-family bandit model with parameters `θ = (θ_1, …, θ_K) ∈ Θ^K`: arm `a`
(0-based) has reward law `ν_{θ_a}`; its mean is `ḃ(θ_a)`. -/
noncomputable def expFamilyBandit {K : ℕ} (F : ExpFamily) (θ : Fin K → F.Θ) :
    BanditAlgorithm.StochasticBandit K where
  P a := F.arm (θ a : ℝ)
  prob a := F.isProbabilityMeasure_arm (θ a).2

/-- The vector of arm means `μ = (ḃ(θ_1), …, ḃ(θ_K))` of the model with parameters `θ`. -/
noncomputable def meanVec {K : ℕ} (F : ExpFamily) (θ : Fin K → F.Θ) : Fin K → ℝ :=
  fun a => deriv F.b (θ a : ℝ)

/-- The class `𝒮` of p. 4, in the natural parameterization: parameter vectors `θ ∈ Θ^K` whose
model has a unique optimal arm, `ḃ(θ_a) > ḃ(θ_i)` for some `a` and every `i ≠ a`. -/
def Sθ (F : ExpFamily) (K : ℕ) : Set (Fin K → F.Θ) :=
  {θ | ∃ a, ∀ i, i ≠ a → deriv F.b (θ i : ℝ) < deriv F.b (θ a : ℝ)}

/-- The class `𝒮` as a set of bandit environments: the models `expFamilyBandit F θ`, `θ ∈ 𝒮`.
This is the class over which `Alt(μ)` and `T*(μ)` (`BanditAlgorithm.baiComplexity`) are taken. -/
def modelClass (F : ExpFamily) (K : ℕ) : Set (BanditAlgorithm.StochasticBandit K) :=
  expFamilyBandit F '' Sθ F K

end OptimalBAI.TrackStop


