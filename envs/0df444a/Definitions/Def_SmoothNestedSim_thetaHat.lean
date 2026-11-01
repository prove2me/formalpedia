-- Prove2me | Definitions.Def_SmoothNestedSim_thetaHat
-- name    : SmoothNestedSim_thetaHat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:40:09.904654+00:00
-- url     : https://prove2.me/theorems/f40e8ecc-01bf-4103-b4f2-49a707d3ea63
-- title:
--   KRR-driven estimator $\hat\theta_{n,m}$ of a nested expectation, (7)
-- statement:
--   For $\mathcal T(\cdot)=\mathbb E[\eta(\cdot)]$, the **KRR-driven nested simulation estimator** is
--
--   $$
--   \hat\theta_{n,m} := \frac1n\sum_{i=1}^n\eta\bigl(\hat f(\mathbf x_i)\bigr),
--   $$
--
--   where $\hat f$ is the KRR fit of the data. It replaces the inner averages $\bar y_i$ of standard nested simulation by the KRR fit, which pools information across scenarios.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §3.2, (7) (first line), p.12

import Mathlib
import Definitions.Def_SmoothNestedSim_krrFit

namespace SmoothNestedSim

/-- **The KRR-driven estimator of a nested expectation** (Wang, Wang, Zhang, *Smooth Nested
Simulation*, arXiv:2201.02958v6, §3.2, (7), first line, p.12):
`θ̂_{n,m} := n⁻¹ Σᵢ η(f̂(xᵢ))` if `𝒯(·) = 𝔼[η(·)]`, where `f̂` is the KRR fit of the data
`ω = (x, ϵ)` (`krrFit`). -/
noncomputable def thetaHat (ν ℓ lam : ℝ) {d n m : ℕ} (η : ℝ → ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (ω : (Fin n → EuclideanSpace ℝ (Fin d)) × (Fin n → Fin m → ℝ)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, η (krrFit ν ℓ lam f ω (ω.1 i))

end SmoothNestedSim


