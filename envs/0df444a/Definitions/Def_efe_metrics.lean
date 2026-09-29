-- Prove2me | Definitions.Def_efe_metrics
-- name    : efe_metrics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T23:39:47.713995+00:00
-- url     : https://prove2.me/theorems/8a3144c9-3339-4750-a12a-e9cbf5711323
-- title:
--   Minkowski and Schwarzschild metrics in coordinates
-- statement:
--   Two concrete metrics in the coordinate framework of `efe_geometry`.
--
--   The **Minkowski metric** of flat spacetime in inertial coordinates is the constant diagonal metric $\operatorname{diag}(-1, 1, 1, 1)$, of signature $(-,+,+,+)$.
--
--   The **Schwarzschild metric** of mass $M$, in Schwarzschild coordinates $x = (t, r, \theta, \varphi)$ and geometrized units $G = c = 1$, is the diagonal metric
--
--   $$g \;=\; \operatorname{diag}\!\left(-\left(1-\frac{2M}{r}\right),\; \left(1-\frac{2M}{r}\right)^{-1},\; r^{2},\; r^{2}\sin^{2}\theta\right),$$
--
--   where $r = x^1$ and $\theta = x^2$.
--
--   Its **exterior region** is the set of coordinate points with $r > 2M$ and $0 < \theta < \pi$: outside the horizon, and away from the coordinate poles where the angular part of the chart degenerates. On this region the four component functions are smooth and the metric matrix is invertible, which is what makes the curvature quantities of `efe_geometry` meaningful there.
-- source:
--   Wikipedia, "Einstein field equations", https://en.wikipedia.org/wiki/Einstein_field_equations (section "Vacuum field equations"); Wikipedia, "General relativity", https://en.wikipedia.org/wiki/General_relativity (section "Solutions — the Schwarzschild solution")

import Definitions.Def_efe_geometry

namespace EinsteinFieldEquations

/-- The Minkowski metric of flat spacetime in inertial coordinates, with signature
`(−, +, +, +)`. -/
noncomputable def minkowski : Tensor2Field := fun _ =>
  Matrix.diagonal ![-1, 1, 1, 1]

/-- The Schwarzschild metric of mass `M` in Schwarzschild coordinates
`x = (t, r, θ, φ)`, in geometrized units `G = c = 1` and signature `(−, +, +, +)`:
`diag(−(1 − 2M/r), (1 − 2M/r)⁻¹, r², r² sin²θ)`. -/
noncomputable def schwarzschild (M : ℝ) : Tensor2Field := fun x =>
  Matrix.diagonal ![-(1 - 2 * M / x 1), (1 - 2 * M / x 1)⁻¹, (x 1) ^ 2,
    (x 1) ^ 2 * Real.sin (x 2) ^ 2]

/-- The Schwarzschild exterior region in Schwarzschild coordinates: the radial coordinate is
outside the horizon, `r > 2M`, and the polar angle avoids the coordinate poles, `0 < θ < π`. -/
def SchwarzschildExterior (M : ℝ) (x : Coord) : Prop :=
  2 * M < x 1 ∧ 0 < x 2 ∧ x 2 < Real.pi

end EinsteinFieldEquations


