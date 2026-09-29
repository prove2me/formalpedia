-- Prove2me | Definitions.Def_rationalEArithmetic
-- name    : rationalEArithmetic
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-11T15:43:00.264182+00:00
-- url     : https://prove2.me/theorems/34870e9b-b5f9-4295-acd3-05ee826d1a9b
-- title:
--   Rational arithmetic coefficients for E-function specialization
-- statement:
--   For rational normalized coefficients $a_n$, require an exponential bound on $|a_n|$ and positive common denominators $D_n$ of $a_0,\ldots,a_n$ with an exponential bound. A complex formal series satisfies the rational arithmetic condition when its factorial-normalized coefficients are such a sequence. Define its canonical value by $\sum_n [X^n]f\,z^n$. This definition specifies only the coefficient arithmetic; a differential equation is a separate hypothesis in specialization theorems.
-- source:
--   Beukers, A refined version of the Siegel–Shidlovskii theorem, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, definition of E-functions, p. 1; restricted here to rational normalized coefficients.

import Mathlib

noncomputable section
namespace ArithmeticE

/-- Exponential size and common-denominator bounds for rational normalized coefficients. -/
def RationalArithmetic (a : ℕ → ℚ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ (∀ n : ℕ, |(a n : ℝ)| ≤ C^(n+1)) ∧
    ∀ n : ℕ, ∃ D : ℕ, 0 < D ∧ (D:ℝ) ≤ C^(n+1) ∧
      ∀ k ≤ n, ∃ z : ℤ, (D:ℚ)*a k = z

/-- Arithmetic coefficient condition only; differential equations are separate hypotheses. -/
def RationalSeriesArithmetic (f : PowerSeries ℂ) : Prop :=
  ∃ a : ℕ → ℚ, (∀ n, (n.factorial:ℂ)*PowerSeries.coeff n f = (a n:ℂ)) ∧
    RationalArithmetic a

/-- Canonical evaluation; arithmetic coefficient bounds imply convergence everywhere. -/
def seriesValue (f : PowerSeries ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, PowerSeries.coeff n f * z^n

end ArithmeticE


