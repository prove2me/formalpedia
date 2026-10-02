-- Prove2me | Definitions.Def_TeschlQM_MinMax_formDomain
-- name    : TeschlQM_MinMax_formDomain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T21:24:04.051306+00:00
-- url     : https://prove2.me/theorems/dce6e523-996d-4157-91e0-83e28fc24936
-- title:
--   Form domain 𝔔(A) and quadratic form q_A(ψ) = ∫ λ dμ_ψ(λ) (3.50)–(3.51)
-- statement:
--   Let $A = \int \lambda \, dP(\lambda)$ be a self-adjoint operator with projection-valued measure $P$ and spectral measures $\mu_\psi$. The **quadratic form** of $A$ is
--   $$q_A(\psi) = \int_{\mathbb R} \lambda \, d\mu_\psi(\lambda),$$
--   defined for every $\psi$ in the **form domain**
--   $$\mathfrak Q(A) = \mathfrak D(|A|^{1/2}) = \Big\{ \psi \in \mathfrak H \ \Big|\ \int_{\mathbb R} |\lambda| \, d\mu_\psi(\lambda) < \infty \Big\}.$$
--   On $\mathfrak D(A)$ it agrees with $\langle \psi, A\psi \rangle$; this is the meaning of $\langle \psi, A\psi\rangle$ for $\psi \in \mathfrak Q(A)$.
--
--   **Formalization Note.** `formDomain P` and `quadForm P` are defined from the projection-valued measure $P$ taken as data. `quadForm P ψ` is a real Bochner integral; it is only evaluated on $\mathfrak Q(A)$, where the integrand is integrable.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 97, Section 3.1, Eqs. (3.50)–(3.51)

import Mathlib
import Definitions.Def_TeschlQM_Shared_spectralMeasure

open MeasureTheory
open scoped ENNReal

namespace TeschlQM.MinMax

/-- Teschl, p. 97, (3.51): the **form domain** of the self-adjoint operator `A = ∫ λ dP(λ)`,
`𝔔(A) = 𝔇(|A|^{1/2}) = {ψ ∈ ℌ | ∫_ℝ |λ| dμ_ψ(λ) < ∞}`, where `μ_ψ` is the spectral measure of
`ψ` for the projection-valued measure `P` of `A`. -/
def formDomain {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) : Set H :=
  {ψ | ∫⁻ x, (‖x‖₊ : ℝ≥0∞) ∂TeschlQM.Shared.spectralMeasure P ψ < ∞}

/-- Teschl, p. 97, (3.50): the **quadratic form** `q_A(ψ) = ∫_ℝ λ dμ_ψ(λ)` of `A = ∫ λ dP(λ)`,
for `ψ ∈ 𝔔(A)` (where the integral converges absolutely). On `𝔇(A)` it equals `⟨ψ, Aψ⟩`. -/
noncomputable def quadForm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : Set ℝ → (H →L[ℂ] H)) (ψ : H) : ℝ :=
  ∫ x, x ∂TeschlQM.Shared.spectralMeasure P ψ

end TeschlQM.MinMax


