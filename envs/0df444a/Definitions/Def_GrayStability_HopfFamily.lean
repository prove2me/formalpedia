-- Prove2me | Definitions.Def_GrayStability_HopfFamily
-- name    : GrayStability_HopfFamily
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-05T19:01:35.60237+00:00
-- url     : https://prove2.me/theorems/f4a2516a-a41f-455a-98b9-71925926e337
-- title:
--   The family $\alpha_t$ on $S^3$ of Geiges' Remark 2.21(1)
-- statement:
--   On $\mathbb{R}^4$ with coordinates $(x_1,y_1,x_2,y_2)$, the unit sphere is $S^3=F^{-1}(0)$ for $F(y)=|y|^2-1$, viewed as a map to $\mathbb{R}^1$. The one-parameter family of one-forms is
--   $$\alpha_t=(x_1\,dy_1-y_1\,dx_1)+(1+t)(x_2\,dy_2-y_2\,dx_2).$$
--   For $t\ge0$ these are contact forms on $S^3$. The Reeb flow of $\alpha_0$ is the Hopf flow, all of whose orbits are closed; for irrational $t$ the Reeb flow of $\alpha_t$ has exactly two periodic orbits.
--
--   Geiges uses this family to show that contact forms, unlike contact structures, are not stable.
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry Vol. II (2006) 315-382, https://arxiv.org/abs/math/0307242, Remark 2.21 (1), p. 15

import Definitions.Def_GrayStability_Basic

/-!
# The family of contact forms of Geiges, Remark 2.21 (1)

On `S³ ⊂ ℝ⁴` with coordinates `(x₁, y₁, x₂, y₂)`:
`α_t = (x₁ dy₁ - y₁ dx₁) + (1 + t)(x₂ dy₂ - y₂ dx₂)`.
Geiges, *Contact geometry*, arXiv:math/0307242, Remark 2.21 (1), p. 15.
-/

namespace GrayStability

noncomputable section

/-- `S³ = F⁻¹(0)` for `F(y) = |y|² - 1`, as a map to `ℝ¹`. -/
def unitSphereEquation (y : E 4) : Fin 1 → ℝ := fun _ => ∑ i, y i ^ 2 - 1

/-- The coordinate covector `dxᵢ` on `ℝ⁴`. -/
def coordCovector (i : Fin 4) : E 4 →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i

/-- `α_t = (x₁ dy₁ - y₁ dx₁) + (1 + t)(x₂ dy₂ - y₂ dx₂)`, coordinates ordered
`(x₁, y₁, x₂, y₂)`. -/
def hopfFamily (t : ℝ) (y : E 4) : E 4 →L[ℝ] ℝ :=
  (y 0 • coordCovector 1 - y 1 • coordCovector 0) +
    (1 + t) • (y 2 • coordCovector 3 - y 3 • coordCovector 2)

end

end GrayStability


