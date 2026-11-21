-- Prove2me | Definitions.Def_MasulloRH_GaussianThetaApproximation
-- name    : MasulloRH_GaussianThetaApproximation
-- status  : Definition
-- author  : @marozols
-- created : 2026-11-21T01:55:33.768608+00:00
-- url     : https://prove2.me/theorems/6f34c003-4870-4c6a-b83e-256b289a15db
-- title:
--   Finite translate approximation of an explicit theta function in a logarithmic strip
-- statement:
--   The test is the theta sum of the admissible three-scale dyadic Gaussian. A finite sum of its real translates is compared to a normalized Gaussian pulse. The energy is the integral of the squared residual against the maximum of the two exponential endpoint weights when the half-width is nonnegative.
-- source:
--   The dyadic Gaussian is MasulloRH.dyadic_gaussian_theta_mellin (714a2f7b). The compact positive-width norm at Sobolev degree zero is Definition 9.2.2.1, equation (9.2.2.4), of A. M. Masullo, The Music of the Primes, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=412. The normalized pulse and the finite residual are introduced for local zero-exclusion certificates.

import Mathlib

open MeasureTheory
open scoped BigOperators

namespace MasulloRH.GaussianApproximation
noncomputable section

/-- The logarithmic theta sum for the admissible dyadic combination of three Gaussians. -/
def theta (x : ℝ) : ℂ := ∑' k : ℤ, let t := (k:ℝ) * Real.exp x
  ((Real.exp (-Real.pi*t^2) - 3*Real.exp (-Real.pi*(2*t)^2) +
    2*Real.exp (-Real.pi*(4*t)^2) : ℝ) : ℂ)

/-- A normalized Gaussian whose Laplace transform is bounded away from zero through height T. -/
def pulse (T x : ℝ) : ℂ :=
  (((T+1)/Real.sqrt Real.pi : ℝ) : ℂ) * Complex.exp (-((((T+1)*x : ℝ):ℂ)^2))

/-- The physical-space error of one finite linear combination of theta translates. -/
def residual {m : ℕ} (T : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ) (x : ℝ) : ℂ :=
  pulse T x - ∑ i, a i * theta (x-y i)

/-- The squared norm for the endpoint weights of the logarithmic strip [c-b,c+b]. -/
def energy (c b : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, Real.exp (2*c*x+2*b*|x|) * ‖f x‖^2

end
end MasulloRH.GaussianApproximation


