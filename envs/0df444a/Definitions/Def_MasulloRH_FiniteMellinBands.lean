-- Prove2me | Definitions.Def_MasulloRH_FiniteMellinBands
-- name    : MasulloRH_FiniteMellinBands
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-27T04:27:28.505711+00:00
-- url     : https://prove2.me/theorems/7fc194a1-32b2-510b-989d-585f832c6773
-- title:
--   Squared Gaussian Mellin error on a finite band and on two full vertical lines
-- statement:
--   Integrate the sum of the two squared Gaussian Mellin residuals for one rational theta approximation over ordinates from −T to T. The total error is the sum of the full-line integrals. The bounded-fit condition asks for a single finite cap on total error while fitting each finite band at every positive tolerance.
-- source:
--   For the endpoint coefficients in the Masullo fixed Gaussian approximation. https://prove2.me/theorems/be33663c-8108-4788-9dcb-d98644c8a714 The endpoints, rational translates and whole-line Mellin errors are the existing definitions. https://prove2.me/definitions/c39cecac-710f-4f89-a11e-ca40af1e00a3

import Definitions.Def_MasulloRH_VerticalThetaApproximation

namespace MasulloRH.FiniteMellinBands
open MeasureTheory Set GaussianApproximation RationalThetaGrid VerticalThetaApproximation
noncomputable section

def poly {m : ℕ} (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ) (s : ℂ) : ℂ :=
  ∑ i, asComplex (a i) * Complex.exp (s*(y i : ℝ))

def errorDensity {m : ℕ} (L U : ℝ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ) (t : ℝ) : ℝ :=
  ‖VerticalThetaApproximation.spectrum L a y t‖^2 + ‖VerticalThetaApproximation.spectrum U a y t‖^2

def band {m : ℕ} (L U T : ℝ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ) : ℝ :=
  ∫ t in Icc (-T) T, errorDensity L U a y t

def total {m : ℕ} (L U : ℝ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ) : ℝ :=
  mass L a y + mass U a y

def boundedFits (L U : ℝ) : Prop :=
  ∃ B : ℝ, ∀ T ε : ℝ, 0 ≤ T → 0 < ε →
    ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      band L U T a y < ε ∧ total L U a y ≤ B

end
end MasulloRH.FiniteMellinBands


