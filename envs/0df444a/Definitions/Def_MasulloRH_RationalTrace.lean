-- Prove2me | Definitions.Def_MasulloRH_RationalTrace
-- name    : MasulloRH_RationalTrace
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-11-20T19:39:58.343878+00:00
-- url     : https://prove2.me/theorems/94552b2f-d8e8-4719-9670-ee32f82964c3
-- title:
--   Rational trace-formula test functions and geometric/spectral terms
-- statement:
--   Concrete objects for the rational-field, norm-invariant specialization of Masullo Theorem 12.5.1.1: smooth tests compactly supported inside the positive reals and vanishing at 1; the actual real-place and prime-power expressions; nontrivial zeros in a strict symmetric strip; and Mellin values weighted by the analytic order of Mathlib riemannZeta. No trace identity or desired RH consequence is assumed.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, Theorem 12.5.1.1, pp.519–520; F=Q, norm-invariant specialization. Haar normalizations: Definitions A.3.1.2, A.3.2.1 and A.3.2.2. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Nat.Prime.Defs

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology ContDiff

namespace MasulloRH

/-- Smooth test functions on the positive reals, extended by zero to the real line.
The compact support is contained in `(0, ∞)` and the test vanishes at `1`. -/
def IsRationalTraceTest (φ : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioi 0 ∧ φ 1 = 0

/-- The real-place contribution after combining `t` and `t⁻¹` and the two signs.
The remaining integration is with respect to additive Lebesgue measure on `(1,∞)`. -/
noncomputable def realTraceIntegrand (φ : ℝ → ℂ) (t : ℝ) : ℂ :=
  (φ t + φ t⁻¹) * ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ)

/-- The contribution of a prime and a strictly positive exponent `n+1`. -/
noncomputable def primePowerTraceTerm (φ : ℝ → ℂ) (i : Nat.Primes × ℕ) : ℂ :=
  let p : ℝ := (i.1 : ℕ)
  let x : ℝ := p ^ (i.2 + 1)
  ((Real.log p / Real.sqrt x : ℝ) : ℂ) * (φ x + φ x⁻¹)

/-- Nontrivial zeta zeros strictly inside the strip `1/2 + (-α,α)`.
Distinct zero locations are indexed once; multiplicity is supplied in the summand. -/
abbrev ZetaZerosInTraceStrip (α : ℝ) :=
  {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.re - 1 / 2| < α}

/-- Spectral term with the analytic order of the actual Riemann zeta function.
Mathlib's Mellin transform uses `t^(s-1) dt`, equivalently `t^s dt/t`. -/
noncomputable def zetaTraceTerm (φ : ℝ → ℂ) (α : ℝ)
    (ρ : ZetaZerosInTraceStrip α) : ℂ :=
  (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * mellin φ ((ρ : ℂ) - 1 / 2)

end MasulloRH


