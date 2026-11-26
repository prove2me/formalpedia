-- Prove2me | solution 1 for Auto.aux_abs_sqrtGaussianDecayKernel_le_forty_bracket_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:14:57.355219+00:00
-- url     : https://prove2.me/submissions/1a4931d6-b2d9-47f5-9117-b33e90e5c8cd

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
public import Theorems.Thm_Auto_aux_sqrtGaussianKernel_eq_inverseFourier_auxiliaryFunctionB_add_scaledPoisson
public import Theorems.Thm_Auto_aux_norm_inverseFourier_auxiliaryFunctionB_le_thirtyTwo_bracket_sq
public import Theorems.Thm_Auto_aux_scaledPoissonKernel_le_eight_bracket_sq

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    |aux_sqrtGaussianDecayKernel x| ≤ 40 * bracketBump x ^ 2 := by
  have hPoisson_nonneg (y : ℝ) : 0 ≤ aux_scaledPoissonKernel y := by
    unfold aux_scaledPoissonKernel poissonKernel
    positivity
  unfold aux_sqrtGaussianDecayKernel
  rw [aux_sqrtGaussianKernel_eq_inverseFourier_auxiliaryFunctionB_add_scaledPoisson]
  calc
    |(FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x +
        (aux_scaledPoissonKernel x : ℂ)).re| ≤
        ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x +
          (aux_scaledPoissonKernel x : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ +
          ‖(aux_scaledPoissonKernel x : ℂ)‖ := norm_add_le _ _
    _ = ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ +
          aux_scaledPoissonKernel x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hPoisson_nonneg x)]
    _ ≤ 32 * bracketBump x ^ 2 + 8 * bracketBump x ^ 2 :=
      add_le_add (aux_norm_inverseFourier_auxiliaryFunctionB_le_thirtyTwo_bracket_sq x)
        (aux_scaledPoissonKernel_le_eight_bracket_sq x)
    _ = 40 * bracketBump x ^ 2 := by ring
end Auto
