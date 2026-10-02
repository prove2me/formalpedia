-- Prove2me | Definitions.Def_TeschlQM_MinMax_essentialSpectrum
-- name    : TeschlQM_MinMax_essentialSpectrum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T20:58:43.881071+00:00
-- url     : https://prove2.me/theorems/3e0f012b-3f92-41bb-9087-7400563e3c6c
-- title:
--   Discrete spectrum σ_d(A) and essential spectrum σ_ess(A)
-- statement:
--   Let $A$ be a linear operator on a complex Hilbert space $\mathfrak H$ with spectrum $\sigma(A)$. The **discrete spectrum** $\sigma_d(A)$ is the set of all eigenvalues $z$ of $A$ which are discrete (isolated) points of $\sigma(A)$ and whose eigenspace $\operatorname{Ker}(A - z)$ is finite dimensional. The **essential spectrum** is its complement in the spectrum,
--   $$\sigma_{ess}(A) = \sigma(A) \setminus \sigma_d(A).$$
--
--   **Formalization Note.** "Isolated point of $\sigma(A)$" is: there is $\varepsilon > 0$ such that the only point of $\sigma(A)$ within distance $\varepsilon$ of $z$ is $z$ itself. "Eigenvalue" is `eigenspace A z ≠ ⊥` and finite dimensionality is `FiniteDimensional ℂ (eigenspace A z)`. The spectrum is the resolvent spectrum of p. 73 (`TeschlQM.MinMax.spectrum`).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 145, Section 6.4

import Mathlib
import Definitions.Def_TeschlQM_MinMax_spectrum
import Definitions.Def_TeschlQM_MinMax_eigenspace

namespace TeschlQM.MinMax

/-- Teschl, p. 145: the **discrete spectrum** `σ_d(A)`, the set of all eigenvalues of `A` which
are discrete (isolated) points of the spectrum `σ(A)` and whose eigenspace is finite
dimensional. -/
def discreteSpectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | z ∈ spectrum A ∧ eigenspace A z ≠ ⊥ ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ spectrum A, ‖w - z‖ < ε → w = z) ∧
    FiniteDimensional ℂ (eigenspace A z)}

/-- Teschl, p. 145: the **essential spectrum** `σ_ess(A) = σ(A) \ σ_d(A)`. -/
def essentialSpectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  spectrum A \ discreteSpectrum A

end TeschlQM.MinMax


