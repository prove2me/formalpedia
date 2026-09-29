-- Prove2me | Definitions.Def_Rudin_ch08_fourier
-- name    : Rudin_ch08_fourier
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-12T20:04:48.226177+00:00
-- url     : https://prove2.me/theorems/a16e84ab-b26e-4d39-a42b-ffaac83ec73e
-- title:
--   Orthonormal systems, Fourier coefficients, trigonometric polynomials
-- statement:
--   Rudin's Chapter 8 apparatus for Fourier series. A sequence $\{\varphi_n\}$ is an **orthonormal system** on $[a,b]$ when $\int_a^b \varphi_n \overline{\varphi_m} = 0$ for $n \ne m$ and $\int_a^b |\varphi_n|^2 = 1$ (Definition 8.10), and the **Fourier coefficients** of $f$ relative to it are $c_n = \int_a^b f\overline{\varphi_n}$. For the trigonometric system one has $c_n = \frac{1}{2\pi}\int_{-\pi}^{\pi} f(x)e^{-inx}dx$, the partial sums $s_N(f;x) = \sum_{|n| \le N} c_n e^{inx}$, the norm $\|h\|_2 = ((1/2\pi)\int_{-\pi}^{\pi}|h|^2)^{1/2}$, $2\pi$-periodicity, and **trigonometric polynomials** (Definition 8.9). Complex-valued integrals use the interval integral rather than the real-valued Riemann–Stieltjes integral of the Chapter 6 mission.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, pp. 185-191, Definitions 8.9, 8.10 and Section 8.13

import Mathlib

/-!
# Rudin, Chapter 8 — orthonormal systems and Fourier series

Definitions transcribed from Walter Rudin, *Principles of Mathematical Analysis*, 3rd edition,
Chapter 8 (Definitions 8.9, 8.10, Section 8.13 and equation (86)).

The integrals of Chapter 8 are integrals of complex-valued functions over `[a, b]`; the
Riemann–Stieltjes integral built for Chapter 6 is real-valued, so Mathlib's interval integral
`∫ x in a..b, f x` is used instead.  For the Riemann-integrable integrands Rudin considers, the
two agree, and Rudin himself notes that his hypothesis `f ∈ ℛ` can be weakened.

Mathlib has a Fourier theory on `AddCircle T`; Rudin works with `2π`-periodic functions on `ℝ`
and with general orthonormal systems on an interval, so those are set up here.
-/

namespace Rudin

/-- Rudin, Definition 8.10: `φ` is an **orthonormal system** on `[a, b]`. -/
def IsOrthonormalSystem (φ : ℕ → ℝ → ℂ) (a b : ℝ) : Prop :=
  (∀ m n : ℕ, m ≠ n → (∫ x in a..b, φ n x * (starRingEnd ℂ) (φ m x)) = 0) ∧
    ∀ n : ℕ, (∫ x in a..b, ‖φ n x‖ ^ 2) = 1

/-- Rudin, Definition 8.10, equation (66): the `n`-th Fourier coefficient of `f` relative to an
orthonormal system `φ` on `[a, b]`. -/
noncomputable def genFourierCoeff (f : ℝ → ℂ) (φ : ℕ → ℝ → ℂ) (a b : ℝ) (n : ℕ) : ℂ :=
  ∫ x in a..b, f x * (starRingEnd ℂ) (φ n x)

/-- Rudin, Section 8.13: the `n`-th Fourier coefficient of a `2π`-periodic function with respect
to the trigonometric system, `cₙ = (1/2π) ∫_{-π}^{π} f(x) e^{-inx} dx`. -/
noncomputable def fourierCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ x in (-Real.pi)..Real.pi, f x * Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))

/-- Rudin, Section 8.13, equation (77): the `N`-th partial sum `s_N(f; x)` of the Fourier series
of `f`. -/
noncomputable def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    fourierCoeff f n * Complex.exp ((n : ℂ) * Complex.I * (x : ℂ))

/-- Rudin, Chapter 8, equation (86): the `L²` norm `‖h‖₂ = ((1/2π) ∫_{-π}^{π} |h|²)^{1/2}`. -/
noncomputable def L2Norm (h : ℝ → ℂ) : ℝ :=
  Real.sqrt ((1 / (2 * Real.pi)) * ∫ x in (-Real.pi)..Real.pi, ‖h x‖ ^ 2)

/-- `f` has period `2π`. -/
def HasPeriodTwoPi (f : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, f (x + 2 * Real.pi) = f x

/-- Rudin, Definition 8.9: `P` is a **trigonometric polynomial**, a finite sum
`∑_{n=-N}^{N} cₙ e^{inx}`. -/
def IsTrigPolynomial (P : ℝ → ℂ) : Prop :=
  ∃ (N : ℕ) (c : ℤ → ℂ), ∀ x : ℝ,
    P x = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), c n * Complex.exp ((n : ℂ) * Complex.I * (x : ℂ))

end Rudin


