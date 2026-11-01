-- Prove2me | Definitions.Def_SmoothNestedSim_krrFit
-- name    : SmoothNestedSim_krrFit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:06.488088+00:00
-- url     : https://prove2.me/theorems/9be13514-c930-4027-b732-6d4731e5ee8a
-- title:
--   KRR fit $\hat f$ of the nested simulation data
-- statement:
--   For data $(\mathbf x,\epsilon)$ with inner-level samples $y_{ij}=f(\mathbf x_i)+\epsilon_{ij}$, let $\bar y_i=\frac1m\sum_{j=1}^m y_{ij}$. The **KRR fit** is the closed-form KRR estimator
--
--   $$
--   \hat f(\cdot)=\mathbf r(\cdot)^\top(\mathbf R+n\lambda\mathbf I)^{-1}\bar{\mathbf y}
--   $$
--
--   built from $\mathbf x_1,\dots,\mathbf x_n$ and $\bar{\mathbf y}$ with the Matérn kernel of smoothness $\nu$ and length-scale $\ell$.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §3.2, (4) and (6), p.12; ȳ_i on p.8

import Mathlib
import Definitions.Def_SmoothNestedSim_krrEstimator

namespace SmoothNestedSim

/-- **The KRR fit `f̂` of the nested simulation data** (Wang, Wang, Zhang, *Smooth Nested
Simulation*, arXiv:2201.02958v6, §3.2, (4) and (6), p.12; `ȳᵢ` on p.8): for the data
`ω = (x, ϵ)` with `x = (x₁, …, xₙ)` and inner samples `yᵢⱼ = f(xᵢ) + ϵᵢⱼ`, the averages are
`ȳᵢ = (1/m) Σⱼ yᵢⱼ` and `f̂ = r(·)ᵀ(R + nλI)⁻¹ȳ` is the KRR estimator (6) with the Matérn kernel
of smoothness `ν` and length-scale `ℓ`. -/
noncomputable def krrFit (ν ℓ lam : ℝ) {d n m : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (ω : (Fin n → EuclideanSpace ℝ (Fin d)) × (Fin n → Fin m → ℝ)) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  krrEstimator ν ℓ lam ω.1 (fun i => (1 / (m : ℝ)) * ∑ j, (f (ω.1 i) + ω.2 i j))

end SmoothNestedSim


