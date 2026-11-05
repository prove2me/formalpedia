-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_Market_Phi
-- name    : BauerleRiederMDP_PartialObs_Market_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:15.524929+00:00
-- url     : https://prove2.me/theorems/8e602511-19a9-48a0-b47a-eca0be25a3e6
-- title:
--   The Bayes operator $\Phi(\rho,z)$ of Chapter 6
-- statement:
--   For a belief $\rho\in\mathbb P(E_Y)$ about the current hidden state and an observed relative risk $z\in\mathbb R^d$, the Bayes operator gives the conditional law of the next hidden state:
--   $$
--   \Phi(\rho,z)(C)=\frac{\displaystyle\int_C\Big(\int q^R(z\mid y)\,q^Y(y'\mid y)\,\rho(dy)\Big)\nu(dy')}{\displaystyle\int_{E_Y}\Big(\int q^R(z\mid y)\,q^Y(y'\mid y)\,\rho(dy)\Big)\nu(dy')},\qquad C\in\mathcal B(E_Y).
--   $$
--   This is equation (5.6) for the joint density $q^{Z,Y}(z,y'\mid y)=q^R(z\mid y)\,q^Y(y'\mid y)$ of the market of Chapter 6; there it depends only on $\rho$ and $z$, not on the wealth or the action. It drives the filter recursion $\mu_{n+1}=\Phi(\mu_n,z_{n+1})$.
--
--   **Formalization Note** The quotient is a probability measure when the denominator is positive and finite; for the remaining $z$, a null set under the predictive law $\int Q^R(\cdot\mid y)\rho(dy)$, the book leaves $\Phi$ undefined and Lean returns $\rho$, so that $\Phi$ always takes values in $\mathbb P(E_Y)$.
-- source:
--   Bäuerle & Rieder (2011), eq. (5.6), p.154 (PDF 167); p.177 (PDF 190): 'The Bayes operator Φ depends only on ρ ∈ IP(E_Y) and z ∈ Z'

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BauerleRiederMDP.PartialObs

/-- **The Bayes operator `Φ(ρ, z)`** of Chapter 6.
Bäuerle & Rieder (2011), eq. (5.6), p.154 (PDF 167), specialized as on p.177 (PDF 190): "The
Bayes operator `Φ` depends only on `ρ ∈ IP(E_Y)` and `z ∈ Z`." With the joint density
`q^{Z,Y}(z, y'|y) = q^R(z|y) q^Y(y'|y)` of `Q^{Z,Y}(·|y) = Q^R(·|y) ⊗ Q^Y(·|y)` (§6.1, p.176),
(5.6) reads
`Φ(ρ, z)(C) = ∫_C (∫ q^R(z|y) q^Y(y'|y) ρ(dy)) ν(dy') / ∫_{E_Y} (∫ q^R(z|y) q^Y(y'|y) ρ(dy)) ν(dy')`.

**Formalization Note.** The quotient is a probability measure exactly when the normalizing
constant is positive and finite; for the remaining `z` (a null set under the predictive law
`∫ Q^R(·|y) ρ(dy)` of the next return) the book leaves `Φ(ρ, z)` undefined, and Lean returns `ρ`
there, so that `Φ` maps `IP(E_Y) × ℝ^d` to `IP(E_Y)` as in the book. -/
noncomputable def Market.Phi {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d)
    (ρ : ProbabilityMeasure EY) (z : Fin d → ℝ) : ProbabilityMeasure EY :=
  if h : (∫⁻ y', ∫⁻ y, M.qR y z * M.qY y y' ∂(ρ : Measure EY) ∂M.nu) ≠ 0 ∧
      (∫⁻ y', ∫⁻ y, M.qR y z * M.qY y y' ∂(ρ : Measure EY) ∂M.nu) ≠ ⊤ then
    ⟨(∫⁻ y', ∫⁻ y, M.qR y z * M.qY y y' ∂(ρ : Measure EY) ∂M.nu)⁻¹ •
        M.nu.withDensity (fun y' => ∫⁻ y, M.qR y z * M.qY y y' ∂(ρ : Measure EY)),
      ⟨by
        rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
          smul_eq_mul]
        exact ENNReal.inv_mul_cancel h.1 h.2⟩⟩
  else ρ

end BauerleRiederMDP.PartialObs


