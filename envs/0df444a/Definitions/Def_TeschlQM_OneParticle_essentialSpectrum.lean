-- Prove2me | Definitions.Def_TeschlQM_OneParticle_essentialSpectrum
-- name    : TeschlQM_OneParticle_essentialSpectrum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T07:34:59.853686+00:00
-- url     : https://prove2.me/theorems/a8f17a21-8f8a-4cb2-8f27-02f29b331bd2
-- title:
--   Eigenspace, point spectrum σ_p, discrete spectrum σ_d and essential spectrum σ_ess
-- statement:
--   Let $A$ be a linear operator in a complex Hilbert space $\mathfrak H$ with spectrum $\sigma(A)$. For $z \in \mathbb C$ let $\operatorname{Ker}(A - z) = \{\psi \in \mathfrak D(A) \mid A\psi = z\psi\}$; $z$ is an **eigenvalue** if $\operatorname{Ker}(A - z) \neq \{0\}$, and the **point spectrum** $\sigma_p(A)$ is the set of eigenvalues. The **discrete spectrum** $\sigma_d(A)$ is the set of eigenvalues which are isolated points of the spectrum and whose eigenspace is finite dimensional:
--   $$\sigma_d(A) = \{ z \in \sigma(A) \mid \operatorname{Ker}(A - z) \neq \{0\},\ \exists \varepsilon > 0:\ \sigma(A) \cap \{ |w - z| < \varepsilon\} = \{z\},\ \dim \operatorname{Ker}(A - z) < \infty \}.$$
--   The **essential spectrum** is $\sigma_{ess}(A) = \sigma(A) \setminus \sigma_d(A)$.
--
--   For a one-particle Schrödinger operator with decaying potential, $\sigma_{ess} = [0,\infty)$ and the bound states are the discrete eigenvalues below zero.
--
--   **Formalization Note.** The eigenspace is `eigenspace A z`, a `Submodule ℂ H`; "isolated" is an explicit $\varepsilon$-ball in $\mathbb C$, and "finite dimensional" is `FiniteDimensional ℂ (eigenspace A z)`. The characterizations of $\sigma_d$ by spectral projections (6.27) are not used.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 145, Section 6.4; p. 103 (σ_p)

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet

namespace TeschlQM.OneParticle

/-- Teschl, p. 77: the eigenspace `Ker(A - z) = {ψ ∈ 𝔇(A) | Aψ = zψ}` of `A` at `z ∈ ℂ`, as a
subspace of `ℌ`. `z` is an eigenvalue of `A` iff `Ker(A - z) ≠ {0}`. -/
def eigenspace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) : Submodule ℂ H :=
  Submodule.map A.domain.subtype (LinearMap.ker (A.toFun - z • A.domain.subtype))

/-- Teschl, p. 103: the **point spectrum** `σ_p(A)`, the set of eigenvalues of `A`. -/
def pointSpectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | eigenspace A z ≠ ⊥}

/-- Teschl, p. 145: the **discrete spectrum** `σ_d(A)`, the set of all eigenvalues of `A` which
are discrete (isolated) points of the spectrum `σ(A)` and whose eigenspace is finite
dimensional. -/
def discreteSpectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | z ∈ TeschlQM.Shared.spectrum A ∧ eigenspace A z ≠ ⊥ ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ TeschlQM.Shared.spectrum A, ‖w - z‖ < ε → w = z) ∧
    FiniteDimensional ℂ (eigenspace A z)}

/-- Teschl, p. 145: the **essential spectrum** `σ_ess(A) = σ(A) \ σ_d(A)`. -/
def essentialSpectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  TeschlQM.Shared.spectrum A \ discreteSpectrum A

end TeschlQM.OneParticle


