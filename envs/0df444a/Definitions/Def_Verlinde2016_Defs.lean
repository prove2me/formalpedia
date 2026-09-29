-- Prove2me | Definitions.Def_Verlinde2016_Defs
-- name    : Verlinde2016_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-27T22:24:38.93038+00:00
-- url     : https://prove2.me/theorems/cc0b815f-5000-4272-871e-caedbb35d6cf
-- title:
--   Averaged density, slope parameter and partial derivatives (Verlinde 2016, eqs. 7.45-7.46)
-- statement:
--   Definitions shared by the mission.
--
--   - **Averaged density** (eq. 7.45). For a mass profile $M:\mathbb R\to\mathbb R$ and radius $r$, $\bar\rho(r) = \dfrac{3M(r)}{4\pi r^3}$, i.e. $M(r) = \frac{4\pi r^3}{3}\bar\rho(r)$.
--   - **Slope parameter** (eq. 7.46). For a density profile $\rho$, $\beta(r) = -\dfrac{d\log\rho(r)}{d\log r} = -\dfrac{r\,\rho'(r)}{\rho(r)}$.
--   - **Partial derivative.** For $f:\mathbb R^n\to\mathbb R$ and $i\in\{1,\dots,n\}$, $\partial_i f(x)$ is the derivative of $f$ at $x$ in the direction of the $i$-th standard basis vector.
--
--   Lean conventions: division by zero is $0$, and the derivative of a function at a point where it is not differentiable is $0$; all mission statements apply these only at $r>0$ where the profiles are differentiable and positive.
-- source:
--   E. Verlinde, Emergent Gravity and the Dark Universe, SciPost Phys. 2, 016 (2017), arXiv:1611.02269v2, https://arxiv.org/abs/1611.02269, p. 40, eqs. (7.45)-(7.46); partial derivatives as in eq. (7.31), p. 35

import Mathlib

namespace Verlinde2016

open Real

/-- Averaged mass density inside a sphere of radius `r` (eq. (7.45)):
`ρ̄(r) = 3 M(r) / (4 π r³)`, i.e. `M(r) = (4 π r³ / 3) ρ̄(r)`. -/
noncomputable def avgDensity (M : ℝ → ℝ) (r : ℝ) : ℝ :=
  3 * M r / (4 * π * r ^ 3)

/-- Slope parameter (eq. (7.46)): `β(r) = - d log ρ(r) / d log r = - r ρ'(r) / ρ(r)`. -/
noncomputable def slopeParam (ρ : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(r * deriv ρ r / ρ r)

/-- The partial derivative `∂ᵢ f` of a function on Euclidean space `ℝⁿ`
in the direction of the `i`-th standard basis vector. -/
noncomputable def partialDeriv {n : ℕ} (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => fderiv ℝ f x (EuclideanSpace.single i 1)

end Verlinde2016


