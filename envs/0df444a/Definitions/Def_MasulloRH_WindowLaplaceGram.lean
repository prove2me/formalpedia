-- Prove2me | Definitions.Def_MasulloRH_WindowLaplaceGram
-- name    : MasulloRH_WindowLaplaceGram
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-27T01:14:06.397467+00:00
-- url     : https://prove2.me/theorems/546b2dee-add3-4513-8abd-612246adaf3a
-- title:
--   Windowed Laplace evaluations and their Gram matrix
-- statement:
--   Defines a weighted exponential wave, its pairwise kernel, the Laplace moment of a function, and the real quadratic form for finite complex coefficients.
-- source:
--   MasulloRH logarithmic Gaussian-theta approximation, using the public quarter-shift certificate. The parameter is the unshifted zeta variable.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace MasulloRH.WindowLaplaceGram
open MeasureTheory
open scoped ComplexConjugate

noncomputable section

/-- Evaluation wave after dividing by the square root of the window weight. -/
def wave (c b : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (s * (x : ℂ) - ((c*x+b*|x| : ℝ) : ℂ))

/-- The two half-line integrals for a pair of evaluation waves. -/
def kernel (c b : ℝ) (s z : ℂ) : ℂ :=
  1 / (s + conj z - ((2*(c-b) : ℝ) : ℂ)) +
  1 / (((2*(c+b) : ℝ) : ℂ) - (s + conj z))

/-- The Laplace evaluation of a physical-space function. -/
def moment (f : ℝ → ℂ) (s : ℂ) : ℂ := ∫ x : ℝ, Complex.exp (s*x)*f x

/-- Squared norm of the linear combination of waves when their real parts lie in the window. -/
def gramValue {n : ℕ} (c b : ℝ) (s d : Fin n → ℂ) : ℝ :=
  (∑ i, ∑ j, d i * conj (d j) * kernel c b (s i) (s j)).re

end
end MasulloRH.WindowLaplaceGram


