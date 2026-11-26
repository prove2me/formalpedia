-- Prove2me | solution 1 for Auto.aux_sqrtGaussianDecayKernel_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:05:39.8081+00:00
-- url     : https://prove2.me/submissions/d446be51-b22a-45b2-8aac-64b7c7ae2370

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
public import Theorems.Thm_Auto_aux_gaussian_pos
public import Theorems.Thm_Auto_gaussian_continuous
public import Theorems.Thm_Auto_gaussian_fourier_fixed
public import Theorems.Thm_Auto_aux_inverseFourier_comp_mul_pos
public import Theorems.Thm_Auto_aux_sqrtGaussianCoefficient_nonneg
public import Theorems.Thm_Auto_aux_sqrtGaussianFrequencyProfile_hasSum
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
    HasSum (fun n : ℕ => aux_sqrtGaussianCoefficient n *
      gaussianRescale (Real.sqrt (n + 1)) x)
      (aux_sqrtGaussianDecayKernel x) := by
  have hinner : Continuous (fun ξ : ℝ => ⟪ξ, x⟫) := by fun_prop
  have hcircle : Continuous (fun ξ : ℝ => 𝐞 ⟪ξ, x⟫) :=
    Real.continuous_fourierChar.comp hinner
  have hne : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  have hDCT : HasSum
      (fun n : ℕ => ∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ •
        ((aux_sqrtGaussianCoefficient n *
          gaussian (Real.sqrt (n + 1) * ξ) : ℝ) : ℂ))
      (aux_sqrtGaussianKernel x) := by
    have h := MeasureTheory.hasSum_integral_of_dominated_convergence
      (μ := volume)
      (F := fun n : ℕ => fun ξ : ℝ => 𝐞 ⟪ξ, x⟫ •
        ((aux_sqrtGaussianCoefficient n *
          gaussian (Real.sqrt (n + 1) * ξ) : ℝ) : ℂ))
      (f := fun ξ : ℝ => 𝐞 ⟪ξ, x⟫ • (aux_sqrtGaussianFrequencyProfile ξ))
      (fun n : ℕ => fun ξ : ℝ => aux_sqrtGaussianCoefficient n *
        gaussian (Real.sqrt (n + 1) * ξ))
      (by
        intro n
        exact (hcircle.smul (Complex.continuous_ofReal.comp
          (continuous_const.mul (gaussian_continuous.comp
            (continuous_const.mul continuous_id))))).aestronglyMeasurable)
      (by
        intro n
        filter_upwards [] with ξ
        rw [Circle.norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (aux_sqrtGaussianCoefficient_nonneg n)
            (aux_gaussian_pos _).le)])
      (by
        filter_upwards [hne] with ξ hξ
        exact (aux_sqrtGaussianFrequencyProfile_hasSum hξ).summable)
      (by
        apply aux_sqrtGaussianFrequencyProfile_integrable_real.congr
        filter_upwards [hne] with ξ hξ
        exact (aux_sqrtGaussianFrequencyProfile_hasSum hξ).tsum_eq.symm)
      (by
        filter_upwards [hne] with ξ hξ
        have hsum := (Complex.hasSum_ofReal).mpr
          (aux_sqrtGaussianFrequencyProfile_hasSum hξ)
        simpa [Function.comp_def, aux_sqrtGaussianFrequencyProfile] using
          hsum.const_smul (𝐞 ⟪ξ, x⟫))
    simpa [aux_sqrtGaussianKernel, Real.fourierInv_eq] using h
  have hterm (n : ℕ) :
      (∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ •
        ((aux_sqrtGaussianCoefficient n *
          gaussian (Real.sqrt (n + 1) * ξ) : ℝ) : ℂ)) =
        ((aux_sqrtGaussianCoefficient n *
          gaussianRescale (Real.sqrt (n + 1)) x : ℝ) : ℂ) := by
    have hs : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hbase (y : ℝ) :
        FourierTransformInv.fourierInv (fun ξ : ℝ => (gaussian ξ : ℂ)) y =
          (gaussian y : ℂ) := by
      rw [Real.fourierInv_eq_fourier_neg, gaussian_fourier_fixed]
      simp [gaussian, Auto.gaussian]
    have hinv : FourierTransformInv.fourierInv
        (fun ξ : ℝ => (gaussian (Real.sqrt (n + 1) * ξ) : ℂ)) x =
        (gaussianRescale (Real.sqrt (n + 1)) x : ℂ) := by
      rw [aux_inverseFourier_comp_mul_pos
        (fun ξ : ℝ => (gaussian ξ : ℂ)) (Real.sqrt (n + 1)) x hs]
      rw [hbase]
      simp [gaussianRescale]
    calc
      (∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ •
        ((aux_sqrtGaussianCoefficient n *
          gaussian (Real.sqrt (n + 1) * ξ) : ℝ) : ℂ)) =
          ∫ ξ : ℝ, (aux_sqrtGaussianCoefficient n : ℂ) *
            (𝐞 ⟪ξ, x⟫ • (gaussian (Real.sqrt (n + 1) * ξ) : ℂ)) := by
        apply integral_congr_ae
        filter_upwards [] with ξ
        rw [Circle.smul_def, smul_eq_mul, Complex.ofReal_mul,
          Circle.smul_def, smul_eq_mul]
        ring
      _ = (aux_sqrtGaussianCoefficient n : ℂ) *
          ∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ • (gaussian (Real.sqrt (n + 1) * ξ) : ℂ) :=
        integral_const_mul _ _
      _ = (aux_sqrtGaussianCoefficient n : ℂ) *
          FourierTransformInv.fourierInv
            (fun ξ : ℝ => (gaussian (Real.sqrt (n + 1) * ξ) : ℂ)) x := by
        rw [Real.fourierInv_eq]
      _ = ((aux_sqrtGaussianCoefficient n *
            gaussianRescale (Real.sqrt (n + 1)) x : ℝ) : ℂ) := by
        rw [hinv]
        norm_cast
  have hterms :
      (fun n : ℕ => ∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ •
        ((aux_sqrtGaussianCoefficient n *
          gaussian (Real.sqrt (n + 1) * ξ) : ℝ) : ℂ)) =
      fun n : ℕ => ((aux_sqrtGaussianCoefficient n *
        gaussianRescale (Real.sqrt (n + 1)) x : ℝ) : ℂ) := by
    funext n
    exact hterm n
  rw [hterms] at hDCT
  have hreal := Complex.reCLM.hasSum hDCT
  have hsum : HasSum
      (fun n : ℕ => aux_sqrtGaussianCoefficient n *
        gaussianRescale (Real.sqrt (n + 1)) x)
      (aux_sqrtGaussianDecayKernel x) := by
    simpa [Function.comp_def, Complex.reCLM_apply, aux_sqrtGaussianDecayKernel] using hreal
  exact hsum
end Auto
