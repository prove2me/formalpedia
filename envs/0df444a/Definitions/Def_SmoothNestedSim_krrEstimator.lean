-- Prove2me | Definitions.Def_SmoothNestedSim_krrEstimator
-- name    : SmoothNestedSim_krrEstimator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:17.935983+00:00
-- url     : https://prove2.me/theorems/a021c3d0-be20-410f-8f79-08a44a3f7ada
-- title:
--   KRR estimator in closed form $\hat f(\mathbf x)=\mathbf r(\mathbf x)^\top(\mathbf R+n\lambda\mathbf I)^{-1}\bar{\mathbf y}$, (6)
-- statement:
--   Let $\mathbf x_1,\dots,\mathbf x_n\in\mathbb R^d$, $\bar{\mathbf y}=(\bar y_1,\dots,\bar y_n)^\top\in\mathbb R^n$ and $\lambda>0$. The **kernel ridge regression estimator** with the Matérn function $\Psi$ of smoothness $\nu$ and length-scale $\ell$ is
--
--   $$
--   \hat f(\mathbf x) = \mathbf r(\mathbf x)^\top(\mathbf R+n\lambda\mathbf I)^{-1}\bar{\mathbf y},
--   $$
--
--   where $\mathbf r(\mathbf x)=(\Psi(\mathbf x-\mathbf x_1),\dots,\Psi(\mathbf x-\mathbf x_n))^\top$ and $\mathbf R=(\Psi(\mathbf x_i-\mathbf x_j))_{i,j=1}^n$.
--
--   The paper defines $\hat f$ as the minimizer of the regularized least-squares problem (5) and records this closed form as (6); the identity is a milestone of the mission.
--
--   **Formalization Note** The closed form is the definition. The matrix inverse is Lean's total inverse; for $\lambda>0$ the matrix $\mathbf R+n\lambda\mathbf I$ is invertible because $\mathbf R$ is positive semidefinite.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §3.2, (6), p.12

import Mathlib
import Definitions.Def_SmoothNestedSim_matern

namespace SmoothNestedSim

/-- **The KRR estimator in closed form** (Wang, Wang, Zhang, *Smooth Nested Simulation*,
arXiv:2201.02958v6, §3.2, (6), p.12): given outer-level scenarios `x₁, …, xₙ ∈ ℝ^d`, responses
`ȳ = (ȳ₁, …, ȳₙ)` and `λ`,
`f̂(z) = r(z)ᵀ (R + nλI)⁻¹ ȳ`, where `r(z) = (Ψ(z − x₁), …, Ψ(z − xₙ))ᵀ` and
`R = (Ψ(xᵢ − xⱼ))ⁿ_{i,j=1}`, with `Ψ` the Matérn function of smoothness `ν` and length-scale
`ℓ`.

**Formalization Note.** The paper defines `f̂` as the minimizer of (5) and states that it equals
this closed form; the closed form is taken as the definition here, and the statement that it is
the unique minimizer of (5) is the milestone `SmoothNestedSim.eq_6_krr_closed_form`. The inverse
is Mathlib's total `Matrix` inverse; for `λ > 0` the matrix `R + nλI` is invertible because `R`
is positive semidefinite. -/
noncomputable def krrEstimator (ν ℓ lam : ℝ) {d n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d))
    (ybar : Fin n → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun z => dotProduct (fun i => matern ν ℓ (z - x i))
    (Matrix.mulVec (Matrix.of (fun i j => matern ν ℓ (x i - x j)) +
      ((n : ℝ) * lam) • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ ybar)

end SmoothNestedSim


