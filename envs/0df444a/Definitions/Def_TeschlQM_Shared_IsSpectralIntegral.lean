-- Prove2me | Definitions.Def_TeschlQM_Shared_IsSpectralIntegral
-- name    : TeschlQM_Shared_IsSpectralIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T21:19:11.62753+00:00
-- url     : https://prove2.me/theorems/b410ab46-ef2c-4a50-937a-9caef5b4bdfe
-- title:
--   T is the spectral integral P(f) = ∫ f(λ) dP(λ) with domain 𝔇_f (3.25), (3.28)
-- statement:
--   Let $P$ be a projection-valued measure on a complex Hilbert space $\mathfrak H$ with spectral measures $\mu_\psi$, and let $f : \mathbb R \to \mathbb C$ be a function. Its domain is
--   $$\mathfrak D_f = \Big\{ \psi \in \mathfrak H \ \Big|\ \int_{\mathbb R} |f(\lambda)|^2 \, d\mu_\psi(\lambda) < \infty \Big\}.$$
--   An operator $T$ **is the spectral integral** $P(f) = \int_{\mathbb R} f(\lambda)\, dP(\lambda)$ if $\mathfrak D(T) = \mathfrak D_f$ and
--   $$\langle \psi, T\psi \rangle = \int_{\mathbb R} f(\lambda)\, d\mu_\psi(\lambda) \qquad \text{for every } \psi \in \mathfrak D_f .$$
--   Over $\mathbb C$ the quadratic form on the dense domain determines $T$ by polarization, so there is at most one such operator. With $f(\lambda) = \lambda$ this says that $T = \int \lambda \, dP(\lambda)$ is the self-adjoint operator whose projection-valued measure is $P$.
--
--   This one definition is shared by every chunk of the series that uses it and is reviewed once for all of them. It serves:
--
--   - chunk `04-min-max`: p. 119, Theorem 4.12 (i); p. 119, Theorem 4.12 (ii)
--   - chunk `05-rage`: pp. 123–124, Theorem 5.1; p. 128, Theorem 5.6, Eq. (5.13); p. 129, Theorem 5.7, Eq. (5.14); p. 130, Theorem 5.8, Eq. (5.18); p. 130, Corollary 5.9, Eqs. (5.19)–(5.20)
--   - chunk `14-scattering`: p. 248, Lemma 12.1; p. 248, Theorem 12.2, Eq. (12.8); p. 249, Lemma 12.3, Eqs. (12.11)–(12.12); p. 249, Theorem 12.4
--
--   **Formalization Note.** Used in this mission with $f(\lambda) = \lambda$ as the hypothesis that the self-adjoint operator $A$ has projection-valued measure $P_A = P$, the form Theorem 3.7 guarantees. The projection-valued measure is taken as data instead of being constructed from $A$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, pp. 91–92, Section 3.1, Eqs. (3.25), (3.28)

import Mathlib
import Definitions.Def_TeschlQM_Shared_spectralMeasure

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Shared

/-- Teschl, p. 91, (3.25): `𝔇_f = {ψ ∈ ℌ | ∫_ℝ |f(λ)|² dμ_ψ(λ) < ∞}`, the domain of `P(f)`. -/
def spectralDomain {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) : Set H :=
  {ψ | ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂spectralMeasure P ψ < ∞}

/-- Teschl, pp. 90–92, (3.17), (3.25), (3.28): the operator `T` is the spectral integral
`P(f) = ∫_ℝ f(λ) dP(λ)`: its domain is `𝔇_f` and `⟨ψ, Tψ⟩ = ∫_ℝ f(λ) dμ_ψ(λ)` for every `ψ` in
it. For a projection-valued measure there is at most one such operator: over `ℂ` the quadratic
form on the (dense) domain determines the operator by polarization. With `f(λ) = λ` this says
`T = ∫ λ dP(λ)`, the self-adjoint operator whose projection-valued measure is `P` (Thm 3.7). -/
def IsSpectralIntegral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) (T : H →ₗ.[ℂ] H) : Prop :=
  (T.domain : Set H) = spectralDomain P f ∧
  ∀ ψ : T.domain, ⟪(ψ : H), T ψ⟫_ℂ = ∫ x, f x ∂spectralMeasure P ψ

end TeschlQM.Shared


