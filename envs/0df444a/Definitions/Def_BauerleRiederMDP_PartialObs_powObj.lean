-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_powObj
-- name    : BauerleRiederMDP_PartialObs_powObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:05.88837+00:00
-- url     : https://prove2.me/theorems/e81dfbc6-1ce6-424a-82d2-d35dcee29dce
-- title:
--   The objective $\int\!\int v(\Phi(\rho,z))(1+\alpha\cdot z)^\gamma\,Q^R(dz|y)\,\rho(dy)$ of (6.3)
-- statement:
--   For a nonnegative function $v$ on $\mathbb P(E_Y)$, a belief $\rho$, an exponent $\gamma$ and a fraction $\alpha\in\mathbb R^d$,
--   $$
--   \int\!\!\int v\big(\Phi(\rho,z)\big)\big(1+\alpha\cdot z\big)^\gamma\,Q^R(dz\mid y)\,\rho(dy).
--   $$
--   Recursion (6.3) maximizes this over $\alpha\in\tilde A$ with $v=d_{n-1}$.
--
--   **Formalization Note** The integrals are $[0,\infty]$-valued; on $\tilde A$ the base $1+\alpha\cdot z$ is nonnegative almost surely.
-- source:
--   Bäuerle & Rieder (2011), Theorem 6.1.2 a), eq. (6.3), p.178 (PDF 191)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_Phi

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The objective of the power-utility recursion (6.3).**
Bäuerle & Rieder (2011), Theorem 6.1.2 a), eq. (6.3), p.178 (PDF 191): for a function `v` on
`IP(E_Y)`, a belief `ρ` and a fraction `α ∈ ℝ^d`,

`powObj M γ v ρ α = ∫ ∫ v(Φ(ρ, z)) (1 + α · z)^γ Q^R(dz|y) ρ(dy)`;

(6.3) is `d_n(ρ) = sup_{α ∈ Ã} powObj M γ d_{n−1} ρ α`.

**Formalization Note.** `v` and the integrals are `ℝ≥0∞`-valued (the integrand is nonnegative
for `α ∈ Ã`, where `1 + α · z ≥ 0` a.s.); `(1 + α · z)^γ` is `Real.rpow` mapped by
`ENNReal.ofReal`, which only matters on a null set when `α ∈ Ã`. -/
noncomputable def powObj {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d) (γ : ℝ)
    (v : ProbabilityMeasure EY → ℝ≥0∞) (ρ : ProbabilityMeasure EY) (α : Fin d → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ∫⁻ z, v (M.Phi ρ z) * ENNReal.ofReal ((1 + α ⬝ᵥ z) ^ γ) ∂M.QR y ∂(ρ : Measure EY)

end BauerleRiederMDP.PartialObs


