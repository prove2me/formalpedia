-- Prove2me | Definitions.Def_TeschlQM_Algebraic_gaussCore
-- name    : TeschlQM_Algebraic_gaussCore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T01:30:23.060559+00:00
-- url     : https://prove2.me/theorems/3971980b-ee8e-48d3-a592-2fa20a7dbf2f
-- title:
--   The Gauss–polynomial domain 𝔇_ω = span{x^α e^{−ω|x|²/2}} ⊆ L²(ℝⁿ) (8.20), (8.34)
-- statement:
--   Fix $n \in \mathbb N_0$ and $\omega \in \mathbb R$. For a multi-index $\alpha \in \mathbb N_0^n$ write $x^\alpha = x_1^{\alpha_1} \cdots x_n^{\alpha_n}$ and $|x|$ for the Euclidean norm of $x \in \mathbb R^n$. The functions
--   $$x \mapsto x^\alpha e^{-\omega |x|^2/2}, \qquad \alpha \in \mathbb N_0^n,$$
--   span a subspace of the functions $\mathbb R^n \to \mathbb C$, and their classes span the subspace
--   $$\mathfrak D_\omega = \operatorname{span}\{x^\alpha e^{-\omega|x|^2/2} \mid \alpha \in \mathbb N_0^n\} \subseteq L^2(\mathbb R^n).$$
--   For $\omega = 1$ this is the domain $\mathfrak D$ of Teschl (8.20) and (8.34).
--
--   $\mathfrak D$ is the domain on which the angular momentum operators and the harmonic oscillator are studied in Chapter 8.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` with Lebesgue measure `volume`; `gaussMonomial n ω α` is the function, `coreFun n ω` its span among all functions, and `core n ω` the span in `Lp ℂ 2 volume` of the classes a.e. equal to some `gaussMonomial n ω α`. The parameter $\omega$ is kept because (8.39)–(8.41) use the Gaussian $e^{-\omega x^2/2}$ (see the harmonic oscillator item).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 176, Eq. (8.20), and p. 178, Eq. (8.34)

import Mathlib

namespace TeschlQM.Algebraic

open MeasureTheory

/-- The function `x ↦ x^α e^{−ω|x|²/2}` on `ℝⁿ` (`x^α = x₁^{α₁} ⋯ xₙ^{αₙ}`, `α ∈ ℕ₀ⁿ`), with
`|x|` the Euclidean norm. For `ω = 1` these span Teschl's `𝔇` of (8.20)/(8.34), p. 176/178. -/
noncomputable def gaussMonomial (n : ℕ) (ω : ℝ) (α : Fin n → ℕ) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x => ((∏ j : Fin n, x j ^ α j) * Real.exp (-(ω * ‖x‖ ^ 2) / 2) : ℝ)

/-- The linear span, inside the space of all functions `ℝⁿ → ℂ`, of the functions
`x^α e^{−ω|x|²/2}`, `α ∈ ℕ₀ⁿ`. -/
noncomputable def coreFun (n : ℕ) (ω : ℝ) : Submodule ℂ (EuclideanSpace ℝ (Fin n) → ℂ) :=
  Submodule.span ℂ (Set.range (gaussMonomial n ω))

/-- Teschl (8.20)/(8.34): the subspace `𝔇_ω = span{x^α e^{−ω|x|²/2} | α ∈ ℕ₀ⁿ} ⊆ L²(ℝⁿ)`, the span
of the `L²` classes of the functions `gaussMonomial n ω α`. Teschl's `𝔇` is the case `ω = 1`. -/
noncomputable def core (n : ℕ) (ω : ℝ) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
  Submodule.span ℂ
    {ψ | ∃ α : Fin n → ℕ, (ψ : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] gaussMonomial n ω α}

end TeschlQM.Algebraic


