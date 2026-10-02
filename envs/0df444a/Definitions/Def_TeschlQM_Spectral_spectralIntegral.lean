-- Prove2me | Definitions.Def_TeschlQM_Spectral_spectralIntegral
-- name    : TeschlQM_Spectral_spectralIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:26:15.68512+00:00
-- url     : https://prove2.me/theorems/2c61ae6a-f59b-483a-9161-82fef9438590
-- title:
--   The spectral integral $P(f) = \int f(\lambda)\,dP(\lambda)$ with domain $\mathfrak D_f$ (3.25), (3.28)
-- statement:
--   Let $P$ be a projection-valued measure on a complex Hilbert space $\mathfrak H$, with spectral measures $\mu_\psi$, and let $f : \mathbb{R} \to \mathbb{C}$ be a Borel function. Its **domain** is
--   $$\mathfrak D_f = \Big\{\psi \in \mathfrak H \;\Big|\; \int_{\mathbb{R}} |f(\lambda)|^2\, d\mu_\psi(\lambda) < \infty\Big\} \qquad (3.25).$$
--   The **spectral integral** $P(f) = \int_{\mathbb{R}} f(\lambda)\, dP(\lambda)$ is the linear operator with domain $\mathfrak D(P(f)) = \mathfrak D_f$ (3.28) whose quadratic form is
--   $$\langle \psi, P(f)\psi\rangle = \int_{\mathbb{R}} f(\lambda)\, d\mu_\psi(\lambda), \qquad \psi \in \mathfrak D_f \qquad (3.17).$$
--   The book constructs $P(f)$ as $P(f)\psi = \lim_n P(\chi_{\Omega_n} f)\psi$ with $\Omega_n = \{|f| \le n\}$ (3.26)–(3.27); that operator has domain $\mathfrak D_f$ and satisfies (3.17). Conversely, on the complex space $\mathfrak H$ the quadratic form on the subspace $\mathfrak D_f$ determines $\langle\varphi, P(f)\psi\rangle$ for $\varphi, \psi \in \mathfrak D_f$ by polarization, and $\mathfrak D_f$ is dense, so these two properties single out the book's operator.
--
--   **Formalization Note.** Operators are `LinearPMap`s `H →ₗ.[ℂ] H`. `spectralDomain P f` is $\mathfrak D_f$; `IsSpectralIntegral P f T` says $T$ has domain $\mathfrak D_f$ and quadratic form (3.17); `spectralIntegral P f` is an operator with this property, chosen by `Classical.choose` (and the zero operator if there is none, which does not happen for a projection-valued measure and a Borel $f$, by Theorem 3.2). The existence of such an operator is asserted by the milestone for Theorem 3.2, not assumed. The integral in (3.17) is a Bochner integral of $f \in L^2 \subseteq L^1$ of the finite measure $\mu_\psi$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, pp. 90-92, Section 3.1, Eqs. (3.17), (3.25), (3.28)

import Mathlib
import Definitions.Def_TeschlQM_Spectral_spectralMeasure

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral

/-- Teschl, p. 91, (3.25): `𝔇_f = {ψ ∈ H | ∫_ℝ |f(λ)|² dμ_ψ(λ) < ∞}`, the domain of `P(f)`. -/
def spectralDomain {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) : Set H :=
  {ψ | ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂spectralMeasure P ψ < ∞}

/-- Teschl, pp. 90–92, (3.17), (3.25), (3.28): the (possibly unbounded) operator `T` is the
spectral integral `∫_ℝ f(λ) dP(λ)`: its domain is `𝔇_f` and `⟨ψ, Tψ⟩ = ∫_ℝ f(λ) dμ_ψ(λ)` for
every `ψ` in it. For a projection-valued measure and a Borel function `f` there is exactly one
such operator, since `𝔇_f` is a dense subspace and, over `ℂ`, the quadratic form on a dense
subspace determines the operator there by polarization. -/
def IsSpectralIntegral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) (T : H →ₗ.[ℂ] H) : Prop :=
  (T.domain : Set H) = spectralDomain P f ∧
  ∀ ψ : T.domain, ⟪(ψ : H), T ψ⟫_ℂ = ∫ x, f x ∂spectralMeasure P ψ

open Classical in
/-- Teschl, p. 92, (3.28): `P(f) = ∫_ℝ f(λ) dP(λ)` with `𝔇(P(f)) = 𝔇_f`, as a partially defined
linear operator: the operator characterized by `IsSpectralIntegral P f` (the zero operator if no
such operator exists, which never happens for a projection-valued measure and a Borel `f`). -/
noncomputable def spectralIntegral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) : H →ₗ.[ℂ] H :=
  if h : ∃ T, IsSpectralIntegral P f T then h.choose else 0

end TeschlQM.Spectral


