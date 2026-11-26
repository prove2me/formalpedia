-- Prove2me | solution 1 for Auto.aux_sqrtGaussianKernel_eq_inverseFourier_auxiliaryFunctionB_add_scaledPoisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:03:54.330238+00:00
-- url     : https://prove2.me/submissions/dca6e941-99e3-42f9-af89-7ea35c043a0a

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
public import Theorems.Thm_Auto_aux_exp_neg_abs_sqrt_pi_integrable
public import Theorems.Thm_Auto_aux_auxiliaryFunctionB_continuous
public import Theorems.Thm_Auto_aux_inverseFourier_scaledPoissonFrequency
public import Theorems.Thm_Auto_aux_auxiliaryFunctionB_integrable

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution
    (x : ℝ) :
    aux_sqrtGaussianKernel x =
      FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x +
        (aux_scaledPoissonKernel x : ℂ) := by
  have hinner : Continuous (fun ξ : ℝ => ⟪ξ, x⟫) := by fun_prop
  have hcircle : Continuous (fun ξ : ℝ => 𝐞 ⟪ξ, x⟫) :=
    Real.continuous_fourierChar.comp hinner
  have hB : Integrable (fun ξ : ℝ => 𝐞 ⟪ξ, x⟫ • (auxiliaryFunctionB ξ : ℂ)) := by
    refine Integrable.mono
      (f := fun ξ : ℝ => 𝐞 ⟪ξ, x⟫ • (auxiliaryFunctionB ξ : ℂ))
      (g := fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ))
      aux_auxiliaryFunctionB_integrable.ofReal ?_ (ae_of_all _ fun ξ => ?_)
    · exact (hcircle.smul
        (Complex.continuous_ofReal.comp aux_auxiliaryFunctionB_continuous)).aestronglyMeasurable
    · simp [Circle.norm_smul]
  have hE : Integrable (fun ξ : ℝ => 𝐞 ⟪ξ, x⟫ • (aux_scaledPoissonFrequency ξ : ℂ)) := by
    change Integrable (fun ξ : ℝ => 𝐞 ⟪ξ, x⟫ •
      (Real.exp (-|Real.sqrt Real.pi * ξ|) : ℂ))
    refine Integrable.mono
      (f := fun ξ : ℝ => 𝐞 ⟪ξ, x⟫ • (Real.exp (-|Real.sqrt Real.pi * ξ|) : ℂ))
      (g := fun ξ : ℝ => (Real.exp (-|Real.sqrt Real.pi * ξ|) : ℂ))
      aux_exp_neg_abs_sqrt_pi_integrable.ofReal ?_ (ae_of_all _ fun ξ => ?_)
    · exact (hcircle.smul (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp ((continuous_abs.comp
          (continuous_const.mul continuous_id)).neg)))).aestronglyMeasurable
    · simp [Circle.norm_smul]
  have hfreq (ξ : ℝ) : (1 - sqrtOneMinusGaussian ξ : ℝ) =
      auxiliaryFunctionB ξ + aux_scaledPoissonFrequency ξ := by
    simp only [auxiliaryFunctionB, aux_scaledPoissonFrequency, aux_poissonFrequency]
    ring
  rw [aux_sqrtGaussianKernel, Real.fourierInv_eq, Real.fourierInv_eq]
  rw [← aux_inverseFourier_scaledPoissonFrequency x, Real.fourierInv_eq]
  change (∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ • ((1 - sqrtOneMinusGaussian ξ : ℝ) : ℂ)) = _
  have hintegrand : (fun ξ : ℝ => 𝐞 ⟪ξ, x⟫ • ((1 - sqrtOneMinusGaussian ξ : ℝ) : ℂ)) =
      fun ξ : ℝ => 𝐞 ⟪ξ, x⟫ • (auxiliaryFunctionB ξ : ℂ) +
        𝐞 ⟪ξ, x⟫ • (aux_scaledPoissonFrequency ξ : ℂ) := by
    funext ξ
    rw [hfreq, Complex.ofReal_add, smul_add]
  rw [hintegrand, integral_add hB hE]
end Auto
