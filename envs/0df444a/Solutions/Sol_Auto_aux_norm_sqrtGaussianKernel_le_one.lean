-- Prove2me | solution 1 for Auto.aux_norm_sqrtGaussianKernel_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:11:51.662829+00:00
-- url     : https://prove2.me/submissions/24656fb5-a70f-4339-881f-54afc1cad077

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
public import Theorems.Thm_Auto_aux_gaussian_integrable
public import Theorems.Thm_Auto_aux_integral_gaussian
public import Theorems.Thm_Auto_aux_one_sub_sqrtOneMinusGaussian_nonneg
public import Theorems.Thm_Auto_aux_one_sub_sqrtOneMinusGaussian_le_gaussian
public import Theorems.Thm_Auto_aux_sqrtGaussianFrequencyProfile_integrable_real

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    ‖aux_sqrtGaussianKernel x‖ ≤ 1 := by
  rw [aux_sqrtGaussianKernel, Real.fourierInv_eq]
  unfold aux_sqrtGaussianFrequencyProfile
  calc
    ‖∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ • ((1 - sqrtOneMinusGaussian ξ : ℝ) : ℂ)‖ ≤
        ∫ ξ : ℝ, ‖𝐞 ⟪ξ, x⟫ • ((1 - sqrtOneMinusGaussian ξ : ℝ) : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ : ℝ, 1 - sqrtOneMinusGaussian ξ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [Circle.norm_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (aux_one_sub_sqrtOneMinusGaussian_nonneg ξ)]
    _ ≤ ∫ ξ : ℝ, gaussian ξ := by
      apply integral_mono aux_sqrtGaussianFrequencyProfile_integrable_real aux_gaussian_integrable
      intro ξ
      exact aux_one_sub_sqrtOneMinusGaussian_le_gaussian ξ
    _ = 1 := aux_integral_gaussian
end Auto
