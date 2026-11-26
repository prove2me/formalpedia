-- Prove2me | solution 1 for Auto.aux_norm_inverseFourier_auxiliaryFunctionB_le_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:03:58.332978+00:00
-- url     : https://prove2.me/submissions/329a6056-f672-45c6-baeb-7d7a0187c841

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
public import Theorems.Thm_Auto_aux_integral_norm_auxiliaryFunctionB_le_eight

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ ≤ 8 := by
  rw [Real.fourierInv_eq]
  calc
    ‖∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ • (auxiliaryFunctionB ξ : ℂ)‖ ≤
        ∫ ξ : ℝ, ‖𝐞 ⟪ξ, x⟫ • (auxiliaryFunctionB ξ : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ : ℝ, ‖auxiliaryFunctionB ξ‖ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp [Circle.norm_smul]
    _ ≤ 8 := aux_integral_norm_auxiliaryFunctionB_le_eight
end Auto
