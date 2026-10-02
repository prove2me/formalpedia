-- Prove2me | Definitions.Def_TeschlQM_Shared_essentialSpectrum
-- name    : TeschlQM_Shared_essentialSpectrum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T22:45:17.560569+00:00
-- url     : https://prove2.me/theorems/1560065d-666d-4f6b-bc4a-52c7847eb22b
-- title:
--   Discrete spectrum σ_d(A) and essential spectrum σ_ess(A) = σ(A)∖σ_d(A)
-- statement:
--   Let $A$ be a linear operator in a complex Hilbert space $\mathfrak H$ with spectrum $\sigma(A)$. For $z \in \mathbb C$ let $\operatorname{Ker}(A - z) = \{\psi \in \mathfrak D(A) \mid A\psi = z\psi\}$; $z$ is an **eigenvalue** if $\operatorname{Ker}(A - z) \neq \{0\}$. The **discrete spectrum** $\sigma_d(A)$ is the set of all eigenvalues which are discrete points of the spectrum and whose corresponding eigenspace is finite dimensional:
--   $$\sigma_d(A) = \{ z \in \sigma(A) \mid \operatorname{Ker}(A - z) \neq \{0\},\ \exists \varepsilon > 0:\ \sigma(A) \cap \{ |w - z| < \varepsilon\} = \{z\},\ \dim \operatorname{Ker}(A - z) < \infty \}.$$
--   The **essential spectrum** is its complement in the spectrum, $\sigma_{ess}(A) = \sigma(A) \setminus \sigma_d(A)$.
--
--   The essential spectrum is the part of the spectrum that survives compact perturbations; it is the subject of Weyl's theorem.
--
--   This one definition is shared by every chunk of the series that uses it and is reviewed once for all of them. It serves:
--
--   - chunk `08-weyl`: p. 145, Lemma 6.17; p. 146, Lemma 6.18; p. 146, Theorem 6.19; p. 147, Theorem 6.20
--   - chunk `13-hvz`: p. 242, Theorem 11.2
--
--   **Formalization Note.** The eigenspace is `eigenspace A z`, a `Submodule ℂ H`; "isolated" is stated with an explicit $\varepsilon$-ball in $\mathbb C$, and "finite dimensional" is `FiniteDimensional ℂ (eigenspace A z)`. The PVM characterizations (6.27)–(6.28) of the book, valid for self-adjoint $A$, are not used.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 145, Section 6.4

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet

namespace TeschlQM.Shared

/-- Teschl, p. 77: the eigenspace `Ker(A - z) = {ψ ∈ 𝔇(A) | Aψ = zψ}` of `A` at `z ∈ ℂ`, as a
subspace of `ℌ`. `z` is an eigenvalue of `A` iff `Ker(A - z) ≠ {0}`. -/
def eigenspace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) : Submodule ℂ H :=
  Submodule.map A.domain.subtype (LinearMap.ker (A.toFun - z • A.domain.subtype))

/-- Teschl, p. 145: the **discrete spectrum** `σ_d(A)`, the set of all eigenvalues of `A` which
are discrete (isolated) points of the spectrum `σ(A)` and whose eigenspace is finite
dimensional. All three conditions (eigenvalue, isolated, finite multiplicity) are required. -/
def discreteSpectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | z ∈ spectrum A ∧ eigenspace A z ≠ ⊥ ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ spectrum A, ‖w - z‖ < ε → w = z) ∧
    FiniteDimensional ℂ (eigenspace A z)}

/-- Teschl, p. 145: the **essential spectrum** `σ_ess(A) = σ(A) \ σ_d(A)`. -/
def essentialSpectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  spectrum A \ discreteSpectrum A

end TeschlQM.Shared


