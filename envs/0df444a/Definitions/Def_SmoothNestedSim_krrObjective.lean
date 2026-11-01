-- Prove2me | Definitions.Def_SmoothNestedSim_krrObjective
-- name    : SmoothNestedSim_krrObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:19.836215+00:00
-- url     : https://prove2.me/theorems/1992e291-3dc9-4245-a12e-2d2e1c692995
-- title:
--   KRR objective (5)
-- statement:
--   For data $\mathbf x_1,\dots,\mathbf x_n\in\Omega$, $\bar y\in\mathbb R^n$, $\lambda>0$ and a candidate $g\in\mathcal N_\Psi(\Omega)$, the **KRR objective** is
--
--   $$
--   \frac1n\sum_{i=1}^n\bigl(\bar y_i-g(\mathbf x_i)\bigr)^2 + \lambda\|g\|^2_{\mathcal N_\Psi(\Omega)},
--   $$
--
--   the regularized least-squares criterion that kernel ridge regression minimizes over the Matérn RKHS $\mathcal N_\Psi(\Omega)$.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §3.2, (5), p.12

import Mathlib
import Definitions.Def_SmoothNestedSim_maternKernel
import Definitions.Def_SmoothNestedSim_rkhsNorm

namespace SmoothNestedSim

/-- **The KRR objective (5)** (Wang, Wang, Zhang, *Smooth Nested Simulation*,
arXiv:2201.02958v6, §3.2, (5), p.12): for a candidate `g ∈ N_Ψ(Ω)`,
`(1/n) Σᵢ (ȳᵢ − g(xᵢ))² + λ ‖g‖²_{N_Ψ(Ω)}`, where `N_Ψ(Ω)` is the RKHS of the Matérn kernel
of smoothness `ν` and length-scale `ℓ` on `Ω`. -/
noncomputable def krrObjective (ν ℓ lam : ℝ) {d n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (ybar : Fin n → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (ybar i - g (x i)) ^ 2 + lam * rkhsNorm (maternKernel ν ℓ) Ω g ^ 2

end SmoothNestedSim


