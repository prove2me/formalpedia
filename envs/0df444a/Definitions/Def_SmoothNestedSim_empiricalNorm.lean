-- Prove2me | Definitions.Def_SmoothNestedSim_empiricalNorm
-- name    : SmoothNestedSim_empiricalNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:15.957449+00:00
-- url     : https://prove2.me/theorems/3bd356ea-0688-4c60-b144-ea821dc3fa1f
-- title:
--   Empirical semi-norm $\|g\|_n$
-- statement:
--   For points $\mathbf x_1,\dots,\mathbf x_n$ and a function $g$, the **empirical semi-norm** is
--
--   $$
--   \|g\|_n = \Bigl(\frac1n\sum_{i=1}^n g^2(\mathbf x_i)\Bigr)^{1/2}.
--   $$
--
--   It measures functions only through their values at the outer-level scenarios; Proposition 2 bounds $\|\hat f-f\|_n^2$ and Lemma EC.3 normalizes an empirical process by it.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, Lemma EC.3, p.ec11 (PDF p.57)

import Mathlib

namespace SmoothNestedSim

/-- **The empirical semi-norm** `‖g‖_n = (n⁻¹ Σᵢ g²(xᵢ))^{1/2}` of a function `g` at the
points `x₁, …, xₙ` (Wang, Wang, Zhang, *Smooth Nested Simulation*, arXiv:2201.02958v6,
Lemma EC.3, p.ec11 = PDF p.57). -/
noncomputable def empiricalNorm {E : Type*} {n : ℕ} (x : Fin n → E) (g : E → ℝ) : ℝ :=
  Real.sqrt ((1 / (n : ℝ)) * ∑ i, g (x i) ^ 2)

end SmoothNestedSim


