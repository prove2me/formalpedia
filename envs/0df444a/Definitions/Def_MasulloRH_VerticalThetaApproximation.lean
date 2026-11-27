-- Prove2me | Definitions.Def_MasulloRH_VerticalThetaApproximation
-- name    : MasulloRH_VerticalThetaApproximation
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-27T04:02:08.687106+00:00
-- url     : https://prove2.me/theorems/c39cecac-710f-4f89-a11e-ca40af1e00a3
-- title:
--   Mellin residuals and coefficient differences for rational theta translates
-- statement:
--   For a finite rational family of shifts and complex rational coefficients, take the squared Mellin residual on a vertical line. On an expanding Gaussian window, consider pairs of individual endpoint fits on a common list of shifts. Measure their coefficient difference by the squared exponentially weighted sum of its norms times the squared L² norm of the theta multiplier on the upper line.
-- source:
--   For the fixed Gaussian approximation on the expanding windows in the Masullo specialization. https://prove2.me/theorems/a73312ae-c4b7-4b9d-8ac1-61f52cc8523d Uses the published rational theta coefficients and the original left and upper slopes. https://prove2.me/definitions/2a38ffb1-5699-5c80-b096-502d99c96d2a

import Definitions.Def_MasulloRH_RationalThetaGrid
import Mathlib.MeasureTheory.Function.L2Space

namespace MasulloRH.VerticalThetaApproximation
open MeasureTheory GaussianApproximation RationalThetaGrid
noncomputable section

def pointAt (c t : ℝ) : ℂ := (c : ℂ) + (t : ℂ) * Complex.I

def approximation {m : ℕ} (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ) :=
  residual 0 (fun i => asComplex (a i)) (fun i => (y i : ℝ))

def spectrum {m : ℕ} (c : ℝ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ) (t : ℝ) : ℂ :=
  gaussian (pointAt c t) - thetaMultiplier (pointAt c t) *
    ∑ i, asComplex (a i) * Complex.exp (pointAt c t * (y i : ℝ))

def mass {m : ℕ} (c : ℝ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ) : ℝ :=
  ∫ t : ℝ, ‖spectrum c a y t‖^2

def coefficientCost {m : ℕ} (c : ℝ) (a b : Fin m → ℚ × ℚ) (y : Fin m → ℚ) : ℝ :=
  (∑ i, ‖asComplex (a i) - asComplex (b i)‖ * Real.exp (c * (y i : ℝ)))^2 *
    ∫ t : ℝ, ‖thetaMultiplier (pointAt c t)‖^2

def feasibleCosts (k : ℕ) (τ : ℝ) : Set ℝ :=
  {d | ∃ (m : ℕ) (a b : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
    mass (FixedGaussianTest.left k) a y < τ ∧ mass (FixedGaussianTest.upper k) b y < τ ∧
    d = coefficientCost (FixedGaussianTest.upper k) a b y}

end
end MasulloRH.VerticalThetaApproximation


