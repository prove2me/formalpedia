-- Prove2me | Definitions.Def_GallegoOzerADI_ZeroSetup_DecreasingDifferences
-- name    : GallegoOzerADI_ZeroSetup_DecreasingDifferences
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:53:23.819986+00:00
-- url     : https://prove2.me/theorems/cb883fe8-596c-42b2-98ce-0030fea33e14
-- title:
--   Definition 2 — decreasing differences in $(x, \theta)$
-- statement:
--   Let $f : \mathbb{R} \times \mathbb{R}^n \to \mathbb{R}$. The function $f$ has **decreasing differences in $(x, \theta)$** if
--
--   $$f(x_1, \theta) - f(x_2, \theta) \le f(x_1, \theta') - f(x_2, \theta') \qquad \text{for all } x_1 \ge x_2 \text{ and } \theta \ge \theta',$$
--
--   where $\theta \ge \theta'$ is the componentwise order on $\mathbb{R}^n$. Equivalently, the increment of $f$ in $x$ is nonincreasing in the parameter $\theta$ ($f$ is submodular in $(x, \theta)$).
--
--   In the inventory model with advance demand information, $x$ is the inventory position and $\theta$ the vector of observed demands beyond the protection period; decreasing differences of the cost functions is what makes the optimal order-up-to level increase with observed demand.
--
--   **Formalization Note.** $f$ is written in curried form $f\,x\,\theta$ with $\theta \in \mathbb{R}^n$ represented as a function on $\{0, \dots, n-1\}$, ordered pointwise.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1349, Definition 2, Eq. (7)

import Mathlib

namespace GallegoOzerADI.ZeroSetup

/-- Definition 2 (Gallego–Özer 2001, p. 1349). A function `f : ℝ × ℝⁿ → ℝ`, written in curried
form `f x θ`, has *decreasing differences in `(x, θ)`* if
`f(x₁, θ) − f(x₂, θ) ≤ f(x₁, θ') − f(x₂, θ')` for all `x₁ ≥ x₂` and `θ ≥ θ'`,
where `θ ≥ θ'` is the componentwise order on `ℝⁿ = Fin n → ℝ`. -/
def DecreasingDifferences {n : ℕ} (f : ℝ → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (x₁ x₂ : ℝ) (θ θ' : Fin n → ℝ), x₂ ≤ x₁ → θ' ≤ θ →
    f x₁ θ - f x₂ θ ≤ f x₁ θ' - f x₂ θ'

end GallegoOzerADI.ZeroSetup


