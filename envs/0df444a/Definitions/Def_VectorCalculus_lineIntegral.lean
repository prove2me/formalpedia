-- Prove2me | Definitions.Def_VectorCalculus_lineIntegral
-- name    : VectorCalculus_lineIntegral
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T00:01:26.179333+00:00
-- url     : https://prove2.me/theorems/d0af5c26-584e-4143-adde-9768c5ccde6b
-- title:
--   Line integral of a vector field along a parametrised curve
-- statement:
--   For a vector field $\mathbf F:\mathbb R^n\to\mathbb R^n$ and a parametrised curve $x:\mathbb R\to\mathbb R^n$, the line integral between parameter values $a$ and $b$ is
--
--   $$\int_C \mathbf F\cdot d\mathbf x \;=\; \int_a^b \sum_{i} F_i\bigl(x(t)\bigr)\,\frac{dx_i}{dt}(t)\,dt,$$
--
--   the dot product of the field along the curve with the curve's velocity, integrated over the parameter interval.
-- source:
--   David Tong, Vector Calculus, University of Cambridge Part IA Mathematical Tripos lecture notes, http://www.damtp.cam.ac.uk/user/tong/vc.html, §1.2.2 (pp. 16–17), the definition of $\int_C \mathbf F\cdot d\mathbf x$

import Mathlib

namespace VectorCalculus

/-- The line integral of a vector field `F` on `ℝⁿ` along the parametrised curve
`x : ℝ → (Fin n → ℝ)` between parameter values `a` and `b`:
`∫_a^b F(x(t)) · x'(t) dt`, where the dot product is the sum over the `n` components
and `x'` is taken componentwise. -/
noncomputable def lineIntegral {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (x : ℝ → (Fin n → ℝ)) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ∑ i, F (x t) i * deriv (fun s => x s i) t

end VectorCalculus


