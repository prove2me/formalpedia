-- Prove2me | Definitions.Def_SchwartzSpaceWiki_Defs
-- name    : SchwartzSpaceWiki_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-13T00:12:08.867473+00:00
-- url     : https://prove2.me/theorems/f0a1bd2a-af1d-4dee-a30a-b1adae0b8316
-- title:
--   Schwartz space $\mathcal{S}(\mathbb{R}^n,\mathbb{C})$ and the Fourier transform
-- statement:
--   Throughout, $\mathbb{R}^n$ is the coordinate space with the Euclidean norm $|x| = (x_1^2+\dots+x_n^2)^{1/2}$ and Lebesgue measure, and a **multi-index** is a tuple $\alpha=(\alpha_1,\dots,\alpha_n)\in\mathbb{N}^n$.
--
--   * For $x\in\mathbb{R}^n$, the **monomial** is $x^\alpha = x_1^{\alpha_1}\cdots x_n^{\alpha_n}$ (with $0^0=1$).
--   * For $f:\mathbb{R}^n\to\mathbb{C}$, the **partial derivative** $\partial_i f(x)$ is the Fréchet derivative of $f$ at $x$ applied to the $i$-th standard basis vector $e_i$, and $D^\beta f = \partial_1^{\beta_1}\partial_2^{\beta_2}\cdots\partial_n^{\beta_n} f$.
--   * The quantity $\|f\|_{\alpha,\beta} = \sup_{x\in\mathbb{R}^n} |x^\alpha (D^\beta f)(x)|$ is taken in $[0,\infty]$, so an unbounded supremum equals $\infty$.
--   * The **Schwartz space** is
--   $$\mathcal{S}(\mathbb{R}^n,\mathbb{C}) = \{\, f\in C^\infty(\mathbb{R}^n,\mathbb{C}) : \|f\|_{\alpha,\beta}<\infty \text{ for all } \alpha,\beta\in\mathbb{N}^n \,\}.$$
--   * The **Fourier transform** of $f:\mathbb{R}^n\to\mathbb{C}$ is $(\mathcal{F}f)(\xi) = \int_{\mathbb{R}^n} e^{-2\pi i\langle x,\xi\rangle} f(x)\,dx$ (Bochner integral with respect to Lebesgue measure; it equals $0$ when the integrand is not integrable). The source does not fix a normalisation; this is the standard $e^{-2\pi i\langle x,\xi\rangle}$ convention.
-- source:
--   Wikipedia, "Schwartz space", revision oldid=1360762580 (https://en.wikipedia.org/w/index.php?title=Schwartz_space&oldid=1360762580), section "Definition"; Fourier transform from the lead paragraph and "Analytic properties", 3rd bullet

import Mathlib

/-!
# Schwartz space (Wikipedia) — definitions

Draft definition file for the Prove2Me mission proposal
"Schwartz Space (Wikipedia): the Fourier transform is an automorphism of 𝒮(ℝⁿ)".
Platform name: `SchwartzSpaceWiki_Defs` (imported as `Definitions.Def_SchwartzSpaceWiki_Defs`).
-/

namespace SchwartzSpaceWiki

open scoped ENNReal

/-- The coordinate space `ℝⁿ` with its Euclidean norm `|x| = (∑ xᵢ²)^{1/2}`. -/
abbrev Rn (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- A multi-index `α = (α₁, …, αₙ) ∈ ℕⁿ`. -/
abbrev MultiIndex (n : ℕ) : Type := Fin n → ℕ

/-- The partial derivative `∂f/∂xᵢ`, i.e. the (Fréchet) derivative of `f` at `x`
applied to the `i`-th standard basis vector `eᵢ`. -/
noncomputable def partialDeriv {n : ℕ} (i : Fin n) (f : Rn n → ℂ) : Rn n → ℂ :=
  fun x => fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The multi-index derivative `D^β f = ∂₁^{β₁} ∂₂^{β₂} ⋯ ∂ₙ^{βₙ} f`. -/
noncomputable def iteratedPartialDeriv {n : ℕ} (β : MultiIndex n) (f : Rn n → ℂ) :
    Rn n → ℂ :=
  (List.finRange n).foldr (fun i g => (partialDeriv i)^[β i] g) f

/-- The monomial `x^α = x₁^{α₁} ⋯ xₙ^{αₙ}`. -/
def monomial {n : ℕ} (α : MultiIndex n) (x : Rn n) : ℝ := ∏ i, (x i) ^ (α i)

/-- The quantity `‖f‖_{α,β} = sup_{x ∈ ℝⁿ} |x^α (D^β f)(x)|`, valued in `[0, ∞]`
(so that an unbounded supremum is `∞`, not a junk value). -/
noncomputable def schwartzSeminorm {n : ℕ} (α β : MultiIndex n) (f : Rn n → ℂ) : ℝ≥0∞ :=
  ⨆ x : Rn n, ‖(monomial α x : ℂ) * iteratedPartialDeriv β f x‖ₑ

/-- The Schwartz space `𝒮(ℝⁿ, ℂ) = { f ∈ C^∞(ℝⁿ, ℂ) : ‖f‖_{α,β} < ∞ for all α, β ∈ ℕⁿ }`. -/
def schwartzSpace (n : ℕ) : Set (Rn n → ℂ) :=
  {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ α β : MultiIndex n, schwartzSeminorm α β f < ⊤}

/-- The Fourier transform `(𝓕 f)(ξ) = ∫_{ℝⁿ} e^{-2πi⟨x, ξ⟩} f(x) dx`
(Lebesgue measure; the Bochner integral, which is `0` for non-integrable `f`). -/
noncomputable def fourierTransform {n : ℕ} (f : Rn n → ℂ) (ξ : Rn n) : ℂ :=
  ∫ x : Rn n, Complex.exp (-(2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) * f x

end SchwartzSpaceWiki


