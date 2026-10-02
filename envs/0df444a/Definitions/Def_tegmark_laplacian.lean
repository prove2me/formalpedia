-- Prove2me | Definitions.Def_tegmark_laplacian
-- name    : tegmark_laplacian
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T02:07:28.664986+00:00
-- url     : https://prove2.me/theorems/2d6975f2-a456-494d-92b2-f7cd997ee93c
-- title:
--   Laplacian on $\mathbb R^n$
-- statement:
--   For a function $f:\mathbb R^n\to\mathbb R$ and a point $x\in\mathbb R^n$, the **Laplacian** is
--   $$\nabla^2 f(x)=\sum_{i=1}^n \frac{\partial^2 f}{\partial x_i^2}(x)=\sum_{i=1}^n D^2 f(x)(e_i,e_i),$$
--   where $e_1,\dots,e_n$ is the standard basis and $D^2 f(x)$ is the second Fréchet derivative.
--
--   It appears in the Poisson equation $\nabla^2\phi=\rho$ for the electrostatic or gravitational potential, in the wave and Klein–Gordon equations, and in Ásgeirsson's ultrahyperbolic equation.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. When $f$ is not twice differentiable at $x$, Lean's derivative conventions give a junk value (typically $0$), so statements using the Laplacian must assume enough regularity themselves.
-- source:
--   M. Tegmark, *On the dimensionality of spacetime*, Class. Quantum Grav. 14 (1997) L69–L75, https://doi.org/10.1088/0264-9381/14/4/002, p. L70 (Poisson equation $\nabla^2\phi=\rho$)

import Mathlib

namespace TegmarkDimensionality

/-- The Laplacian `∇² f (x) = ∑ᵢ ∂²f/∂xᵢ² (x)` of a real function on `ℝⁿ`, written as the sum
of the pure second derivatives along the standard coordinate directions. -/
noncomputable def laplacian {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, iteratedFDeriv ℝ 2 f x ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]

end TegmarkDimensionality


