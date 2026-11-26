-- Prove2me | solution 1 for Auto.aux_integral_norm_auxiliaryFunctionBTrueSecondDerivative_le_fiftySix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:06:14.313204+00:00
-- url     : https://prove2.me/submissions/9b1aa90e-87d7-4067-85c3-e491a912ccc9

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_Notation
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Definitions.Def_LeanNct_Auto_Preliminaries_Gaussians
public import Theorems.Thm_Auto_aux_integral_norm_auxiliaryFunctionBSecondDerivative_le_fiftySix

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    (∫ ξ : ℝ, ‖if ξ = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative ξ‖) ≤ 56 := by
  have hne : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  calc
    (∫ ξ : ℝ, ‖if ξ = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative ξ‖) =
        ∫ ξ : ℝ, ‖auxiliaryFunctionBSecondDerivative ξ‖ := by
      apply integral_congr_ae
      filter_upwards [hne] with ξ hξ
      simp [hξ]
    _ ≤ 56 := aux_integral_norm_auxiliaryFunctionBSecondDerivative_le_fiftySix
end Auto
