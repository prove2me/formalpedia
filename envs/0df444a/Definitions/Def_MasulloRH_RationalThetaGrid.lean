-- Prove2me | Definitions.Def_MasulloRH_RationalThetaGrid
-- name    : MasulloRH_RationalThetaGrid
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T22:25:10.793399+00:00
-- url     : https://prove2.me/theorems/2a38ffb1-5699-5c80-b096-502d99c96d2a
-- title:
--   Regularized dyadic theta multiplier and factorial Gaussian Gram matrices
-- statement:
--   Defines the entire theta Mellin multiplier, the Gaussian transform, their determinant at two frequencies, and the real Gaussian Gram matrix for the rational shifts from −n to n at spacing 1/n!.
-- source:
--   Masullo RH specialization, fixed unit Gaussian in the expanding weighted windows. The dyadic theta Mellin identity and the accepted finite-window energy identities are used at their registered types. https://prove2.me/theorems/28908aa5-2420-4285-97be-cda4701d769b

import Definitions.Def_MasulloRH_FixedGaussianTest
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory
open scoped ComplexConjugate
namespace MasulloRH.RationalThetaGrid
open GaussianApproximation FixedGaussianTest
noncomputable section

def logTwo : ℂ := (Real.log 2 : ℝ)
def regZ (s : ℂ) := s*(1-s)*completedRiemannZeta₀ s-1
def thetaMultiplier (s : ℂ) : ℂ :=
  -logTwo^2 * dslope Complex.exp 0 (-logTwo*s) * dslope Complex.exp 0 (logTwo*(1-s)) * regZ s
def gaussian (s : ℂ) := Complex.exp (s^2/4)
def vertical (t : ℝ) : ℂ := (t:ℂ)*Complex.I
def point (t : ℝ) : ℂ := 1+vertical t
def phase (t : ℝ) : ℂ := Complex.exp (-logTwo*vertical t)
def defect (s : ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  thetaMultiplier s * gaussian (s+vertical t) - z*thetaMultiplier (s+vertical t)*gaussian s

def asComplex (v : ℚ × ℚ) : ℂ := (v.1:ℂ)+(v.2:ℂ)*Complex.I
def gridCount (n : ℕ) := 2*(n*n.factorial)+1
def mesh (n : ℕ) (i : Fin (gridCount n)) : ℚ :=
  ((i.val:ℚ)-(n*n.factorial:ℕ))/(n.factorial:ℚ)
def gram {m : ℕ} (c b : ℝ) (y : Fin m → ℚ) : Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
  let u : Fin (m+1) → ℝ → ℂ := Fin.cons (pulse 0) (fun i x => theta (x-(y i:ℝ)))
  fun i j => (∫ x : ℝ, (Real.exp (2*c*x+2*b*|x|):ℂ)*conj (u i x)*u j x).re
def passes (j n : ℕ) : Prop :=
  ¬ (gram (fullCenter (j+1)) (fullWidth (j+1)) (mesh n) -
      Matrix.single 0 0 (1/((j:ℝ)+1))).PosSemidef
def tailApprox : Prop :=
  ∀ j : ℕ, 16384 ≤ j → ∃ k : ℕ, j+1 ≤ k ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
    energy (fullCenter k) (fullWidth k) (residual 0 (fun i => asComplex (a i)) (fun i => (y i:ℝ))) < 1/((j:ℝ)+1)
end
end MasulloRH.RationalThetaGrid


