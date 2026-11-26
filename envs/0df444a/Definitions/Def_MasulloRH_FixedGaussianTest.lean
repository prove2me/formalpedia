-- Prove2me | Definitions.Def_MasulloRH_FixedGaussianTest
-- name    : MasulloRH_FixedGaussianTest
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T19:23:08.830005+00:00
-- url     : https://prove2.me/theorems/301c9181-2bf8-5b2d-8998-b54d3a671ea6
-- title:
--   Nested windows for a fixed Gaussian and rational theta translates
-- statement:
--   The left endpoints decrease to one half. One family has fixed right endpoint seven eighths. The other has right endpoints increasing to one. Both use the same unit-width Gaussian. Approximation means that a finite combination of rationally shifted theta functions with rational complex coefficients has arbitrarily small weighted squared error.
-- source:
--   Developed for the Masullo theta-window argument and the centered Möbius target. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Definitions.Def_MasulloRH_GaussianThetaApproximation

namespace MasulloRH.FixedGaussianTest
open GaussianApproximation

noncomputable section

/-- The left edges decrease to one half. The fixed right edge overlaps the proved arithmetic region. -/
def left (k : ℕ) : ℝ := 1/2 + (12287/32768)/((k:ℝ)+1)
def right : ℝ := 7/8
def center (k : ℕ) : ℝ := (left k + right)/2
def width (k : ℕ) : ℝ := (right - left k)/2

/-- Approximation of the same unit-width Gaussian at every precision. -/
def Approximates (k : ℕ) : Prop := ∀ ε : ℝ, 0 < ε →
  ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
    energy (center k) (width k) (residual 0
      (fun i => ((a i).1 : ℂ) + ((a i).2 : ℂ)*Complex.I) (fun i => (y i : ℝ))) < ε

/-- The upper edge stays at seven eighths for the first eight windows, then increases to one. -/
def upper (k : ℕ) : ℝ := max right (1-1/((k:ℝ)+1))
def fullCenter (k : ℕ) : ℝ := (left k+upper k)/2
def fullWidth (k : ℕ) : ℝ := (upper k-left k)/2

def FullApprox (k : ℕ) : Prop := ∀ ε : ℝ, 0<ε →
  ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
    energy (fullCenter k) (fullWidth k) (residual 0
      (fun i => ((a i).1 : ℂ) + ((a i).2 : ℂ)*Complex.I) (fun i => (y i : ℝ))) < ε

end
end MasulloRH.FixedGaussianTest


