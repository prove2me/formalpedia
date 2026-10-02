-- Prove2me | Definitions.Def_TeschlQM_Spectral_boundedSpectralIntegral
-- name    : TeschlQM_Spectral_boundedSpectralIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:26:48.533274+00:00
-- url     : https://prove2.me/theorems/0de2d5eb-c625-4161-a28c-e546533d006e
-- title:
--   Bounded Borel functions $B(\mathbb{R})$ and the bounded functional calculus $P(f)\in\mathfrak L(\mathfrak H)$ (3.20)
-- statement:
--   A function $f : \mathbb{R} \to \mathbb{C}$ belongs to $B(\mathbb{R})$, the **bounded Borel functions**, if it is Borel measurable and $\sup_{\lambda\in\mathbb{R}} |f(\lambda)| < \infty$; $B(\mathbb{R})$ carries the sup norm.
--
--   For a projection-valued measure $P$ on a complex Hilbert space $\mathfrak H$ and $f \in B(\mathbb{R})$, the operator $P(f) = \int_{\mathbb{R}} f(\lambda)\, dP(\lambda) \in \mathfrak L(\mathfrak H)$ of (3.20) is the bounded operator with
--   $$\langle \psi, P(f)\psi\rangle = \int_{\mathbb{R}} f(\lambda)\, d\mu_\psi(\lambda) \qquad \text{for all } \psi \in \mathfrak H \qquad (3.17).$$
--   The book obtains $P(f)$ by extending $P(\sum_j \alpha_j \chi_{\Omega_j}) = \sum_j \alpha_j P(\Omega_j)$ from simple functions by continuity; the extension satisfies (3.17), and on a complex Hilbert space a bounded operator is determined by its quadratic form, so (3.17) characterizes it.
--
--   **Formalization Note.** `IsBoundedBorel f` is `Measurable f ∧ ∃ C, ∀ x, ‖f x‖ ≤ C`. `boundedSpectralIntegral P f : H →L[ℂ] H` is a bounded operator satisfying (3.17) for every $\psi$, chosen by `Classical.choose`, and $0$ if none exists; that such an operator exists for every $f \in B(\mathbb{R})$ is part of the content of the milestone for Theorem 3.1 (through (3.21) with $g = 1$ and $P(1) = \mathbb{I}$), not an assumption.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 90, Section 3.1, Eqs. (3.17), (3.20)

import Mathlib
import Definitions.Def_TeschlQM_Spectral_spectralMeasure

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral

/-- Teschl, p. 90: `f` belongs to `B(ℝ)`, the bounded Borel functions `ℝ → ℂ`. -/
def IsBoundedBorel (f : ℝ → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C

open Classical in
/-- Teschl, p. 90, (3.17), (3.20): for a bounded Borel function `f`, `P(f) = ∫_ℝ f(λ) dP(λ)` as a
bounded operator on `H`: the bounded operator `T` with `⟨ψ, Tψ⟩ = ∫_ℝ f(λ) dμ_ψ(λ)` for all
`ψ ∈ H` (over `ℂ` a bounded operator is determined by its quadratic form); the zero operator if
there is none, which never happens for a projection-valued measure and `f ∈ B(ℝ)`. -/
noncomputable def boundedSpectralIntegral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) : H →L[ℂ] H :=
  if h : ∃ T : H →L[ℂ] H, ∀ ψ : H, ⟪ψ, T ψ⟫_ℂ = ∫ x, f x ∂spectralMeasure P ψ then h.choose
  else 0

end TeschlQM.Spectral


