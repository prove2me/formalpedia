-- Prove2me | Definitions.Def_SuttonBartoRL_PolicyGradient_GaussianPolicy
-- name    : SuttonBartoRL_PolicyGradient_GaussianPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:56:04.229352+00:00
-- url     : https://prove2.me/theorems/6daa039d-8406-4b4d-a3cd-164630cf1aa2
-- title:
--   The Gaussian policy (13.19) with linear mean and log-linear standard deviation (13.20)
-- statement:
--   For a real-valued scalar action $a$ the **Gaussian policy** is the normal density
--   $$
--   \pi(a \mid s, \theta) = \frac{1}{\sigma(s,\theta)\sqrt{2\pi}} \exp\!\Big(-\frac{(a - \mu(s,\theta))^2}{2\sigma(s,\theta)^2}\Big),
--   $$
--   where the parameter is split as $\theta = [\theta_\mu, \theta_\sigma]^\top$, the mean is linear in state features and the standard deviation is the exponential of a linear function:
--   $$
--   \mu(s,\theta) = \theta_\mu^\top x_\mu(s), \qquad \sigma(s,\theta) = \exp\big(\theta_\sigma^\top x_\sigma(s)\big).
--   $$
--
--   It is the book's standard parameterization for continuous action spaces.
--
--   **Formalization Note** $\theta_\mu \in \mathbb R^{d_\mu}$ and $\theta_\sigma \in \mathbb R^{d_\sigma}$ are separate arguments; $\sigma > 0$ always.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (13.19)–(13.20), pp. 335–336

import Mathlib

namespace SuttonBartoRL.PolicyGradient

variable {S : Type} {dμ dσ : ℕ}

/-- (13.20), p. 336: the mean `µ(s, θ) = θ_µᵀ x_µ(s)`, linear in state features `x_µ(s)`. -/
noncomputable def gaussMean (xμ : S → EuclideanSpace ℝ (Fin dμ)) (θμ : EuclideanSpace ℝ (Fin dμ)) (s : S) : ℝ :=
  inner ℝ θμ (xμ s)

/-- (13.20), p. 336: the standard deviation `σ(s, θ) = exp(θ_σᵀ x_σ(s))`, always positive. -/
noncomputable def gaussStd (xσ : S → EuclideanSpace ℝ (Fin dσ)) (θσ : EuclideanSpace ℝ (Fin dσ))
    (s : S) : ℝ :=
  Real.exp (inner ℝ θσ (xσ s))

/-- (13.19)–(13.20), pp. 335–336: the **Gaussian policy** over a real-valued scalar action `a`,
with parameter `θ = [θ_µ, θ_σ]ᵀ`:
`π(a | s, θ) = 1 / (σ(s, θ) √(2π)) · exp(−(a − µ(s, θ))² / (2 σ(s, θ)²))`. -/
noncomputable def gaussianPolicy (xμ : S → EuclideanSpace ℝ (Fin dμ))
    (xσ : S → EuclideanSpace ℝ (Fin dσ)) (θμ : EuclideanSpace ℝ (Fin dμ))
    (θσ : EuclideanSpace ℝ (Fin dσ)) (s : S) (a : ℝ) : ℝ :=
  1 / (gaussStd xσ θσ s * Real.sqrt (2 * Real.pi)) *
    Real.exp (-(a - gaussMean xμ θμ s) ^ 2 / (2 * gaussStd xσ θσ s ^ 2))

end SuttonBartoRL.PolicyGradient


