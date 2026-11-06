-- Prove2me | Definitions.Def_GeomDRSub_pd
-- name    : GeomDRSub_pd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:03.355208+00:00
-- url     : https://prove2.me/theorems/4b4a1e06-11bb-4a18-ba24-4e40d75ad592
-- title:
--   Partial derivative $\partial_i f$ on the closed cube
-- statement:
--   For $f:\mathbb R^d\to\mathbb R$, a coordinate $i$ and a point $y$ of the cube, $\partial_i f(y)$ is the derivative of $f$ **within the cube** $[0,1]^d$ at $y$, applied to the coordinate vector $e_i$.
--
--   At interior points this is the usual partial derivative. At boundary points, for $f$ continuously differentiable on the cube, it is the continuous extension of the interior partial derivative, which is the convention of Definition 3.1: "the gradients at the boundary are the continuous extensions of the interior gradients".
--
--   **Formalization Note** The derivative is Mathlib's `fderivWithin ℝ f (cube d)`; the plain Fréchet derivative would vanish by convention at boundary points.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 3.1, p.8, Definition 3.1

import Mathlib
import Definitions.Def_GeomDRSub_cube

namespace GeomDRSub

/-- **Partial derivative `∂ᵢf(y)` on the closed cube.** Aggarwal–Lu, arXiv:2610.00545, Section 3.1,
p.8 (Definition 3.1): "The gradients at the boundary are the continuous extensions of the interior
gradients."

`pd f i y` is the derivative of `f` within the cube `[0,1]^d` at `y`, applied to the `i`-th
coordinate vector `eᵢ`.

**Formalization Note.** The derivative is `fderivWithin ℝ f (cube d)`, not `fderiv`: the objectives
are only meaningful on the cube. For `d ≥ 1` the cube is convex with nonempty interior, hence a set
of unique differentiability, and for `f` continuously differentiable on the cube (`ContDiffOn ℝ 1`)
the within-derivative at a boundary point is the continuous extension of the interior derivative,
which is the paper's boundary convention. -/
noncomputable def pd {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (i : Fin d)
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  fderivWithin ℝ f (cube d) y (EuclideanSpace.single i 1)

end GeomDRSub


