-- Prove2me | Definitions.Def_OptimalBAI_OptProportions_ExpFamily
-- name    : OptimalBAI_OptProportions_ExpFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:56:27.665457+00:00
-- url     : https://prove2.me/theorems/d70be2af-c14f-4f92-8f37-db69ac921c42
-- title:
--   Canonical one-parameter exponential family, its mean space and its divergence $d$
-- statement:
--   A **canonical one-parameter exponential family** is a family of probability laws $(\nu_\theta)_{\theta\in\Theta}$ on $\mathbb R$ with densities
--   $$\frac{d\nu_\theta}{d\xi}(x) = \exp\big(\theta x - b(\theta)\big)$$
--   with respect to a reference measure $\xi$ on $\mathbb R$, where $\Theta\subseteq\mathbb R$ is the parameter set and $b:\Theta\to\mathbb R$ the log-partition function. The structure records:
--
--   1. the reference measure $\xi$, the parameter set $\Theta$ and the function $b$;
--   2. $\Theta$ is a nonempty open interval;
--   3. every $\nu_\theta$, $\theta\in\Theta$, has total mass $1$;
--   4. $b$ is twice continuously differentiable on $\Theta$, and $\ddot b(\theta) > 0$ for every $\theta\in\Theta$.
--
--   The law $\nu_\theta$ has mean $\dot b(\theta)$. The **mean space** is $\dot b(\Theta)$; for $\mu\in\dot b(\Theta)$ we write $\theta(\mu)$ for the unique $\theta\in\Theta$ with $\dot b(\theta)=\mu$. The divergence induced on the mean space by the Kullback–Leibler divergence is
--   $$d(\mu,\mu') = b(\theta') - b(\theta) - \dot b(\theta)(\theta'-\theta), \qquad \theta=\theta(\mu),\ \theta'=\theta(\mu'),$$
--   which is $\mathrm{KL}(\nu_\theta,\nu_{\theta'})$.
--
--   This is the modelling layer of the paper: a bandit model is identified with the vector of means of its arms, and every cost in the optimization problem defining the optimal proportions of arm draws is expressed through $d$.
--
--   **Formalization Note** The paper asks only that $b$ be convex and twice differentiable on $\Theta\subset\mathbb R$. Two conditions are added: $\Theta$ is an open interval, and $\ddot b>0$ on $\Theta$. Strict convexity makes the mean map $\theta\mapsto\dot b(\theta)$ injective, which the paper's "the unique distribution in $\mathcal P$ with expectation $\mu$" requires. The inverse $\theta(\mu)$ is a choice of preimage in $\Theta$ (unique on $\dot b(\Theta)$), and $d$ is only meaningful for $\mu,\mu'\in\dot b(\Theta)$; on the mean space the term $\dot b(\theta)$ equals $\mu$ and is written that way. The measure $\xi$ and the normalization are not used by the statements of this mission; they are kept so that the family is the same object as in the other missions of the series.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 3, §2 (definition of the exponential family and of d)

import Mathlib

open MeasureTheory

namespace OptimalBAI.OptProportions

/-- A canonical one-parameter exponential family (Garivier–Kaufmann, arXiv:1602.04589v2, p. 3, §2):
the laws `ν_θ` on `ℝ` with density `dν_θ/dξ (x) = exp(θ x - b(θ))` with respect to a reference
measure `ξ`, for `θ` in the parameter set `Θ`.

The paper asks that `b` be convex and twice differentiable. Two conditions are added and disclosed:
`Θ` is a nonempty open interval, and `b'' > 0` on `Θ` (strict convexity), which makes the mean map
`θ ↦ b'(θ)` injective, as the paper's "the unique distribution in `𝒫` with expectation `μ`"
requires. `isNormalized` says that every `ν_θ`, `θ ∈ Θ`, is a probability law. (In this mission
only `Θ` and `b` enter the statements; `ξ` and `isNormalized` are kept so that the family is the
same object as in the other missions of the series.) -/
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

end OptimalBAI.OptProportions


