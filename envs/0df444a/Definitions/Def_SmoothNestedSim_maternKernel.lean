-- Prove2me | Definitions.Def_SmoothNestedSim_maternKernel
-- name    : SmoothNestedSim_maternKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:18.727379+00:00
-- url     : https://prove2.me/theorems/e340dc7b-543d-4cb5-9835-5cfe78bdd3d7
-- title:
--   Matérn kernel $k(\mathbf x,\tilde{\mathbf x})=\Psi(\mathbf x-\tilde{\mathbf x})$
-- statement:
--   The **Matérn kernel** of smoothness $\nu$ and length-scale $\ell$ on $\mathbb R^d$ is $k(\mathbf x,\tilde{\mathbf x}) = \Psi(\mathbf x-\tilde{\mathbf x})$, where $\Psi$ is the Matérn function (3).
--
--   It is the kernel whose reproducing kernel Hilbert space $\mathcal N_\Psi(\Omega)$ carries the unknown regression function $f$ (Assumption 3) and in which the KRR estimator is computed.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §3.1, p.11

import Mathlib
import Definitions.Def_SmoothNestedSim_matern

namespace SmoothNestedSim

/-- **The Matérn kernel** `k(x, x̃) = Ψ(x − x̃)` of smoothness `ν` and length-scale `ℓ`
(Wang, Wang, Zhang, *Smooth Nested Simulation*, arXiv:2201.02958v6, §3.1, p.11: "The Matérn
kernel of smoothness `ν` is defined as `k(x, x̃) = Ψ(x − x̃)`"), with `Ψ` the Matérn function
(3). -/
noncomputable def maternKernel (ν ℓ : ℝ) {d : ℕ} :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x x' => matern ν ℓ (x - x')

end SmoothNestedSim


