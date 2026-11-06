-- Prove2me | Definitions.Def_ConstrSOSP_gradVec
-- name    : ConstrSOSP_gradVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:39.770061+00:00
-- url     : https://prove2.me/theorems/7376c4bc-2553-4f4b-ad7e-2d3c27c28dd7
-- title:
--   Gradient $\nabla F(z)$ as a coordinate vector
-- statement:
--   For $F:\mathbb R^d\to\mathbb R$, the gradient at $z$ is the vector of partial derivatives $(\partial F/\partial z_i)(z)$, computed from the Fréchet derivative. For the $C^2$ functions of this mission it is the usual gradient.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.2, p.18

import Mathlib

namespace ConstrSOSP

/-- **Gradient `∇F(z)` as a coordinate vector**: `(∇F(z))ᵢ = ∂F/∂zᵢ (z)`, the Fréchet derivative of
`F` at `z` applied to the `i`-th unit vector (arXiv:2604.02285, 2 Nov 2026, §4.2, p.18, where `f`
is twice differentiable and `∇f` its gradient).

**Formalization Note** Mathlib's `fderiv`; it is the true gradient wherever `F` is
differentiable (all uses are for `C²` functions). -/
noncomputable def gradVec {d : ℕ} (F : (Fin d → ℝ) → ℝ) (z : Fin d → ℝ) : Fin d → ℝ :=
  fun i => fderiv ℝ F z (Pi.single i 1)

end ConstrSOSP


