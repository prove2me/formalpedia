-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionB_eLpNorm_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:50:29.43199+00:00
-- url     : https://prove2.me/submissions/af7b49b0-04a1-44f0-b47b-91b5d268e4f6

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
public import Theorems.Thm_Auto_aux_poissonFrequency_integrable
public import Theorems.Thm_Auto_aux_integral_poissonFrequency
public import Theorems.Thm_Auto_aux_exp_neg_abs_sqrt_pi_le_poissonFrequency
public import Theorems.Thm_Auto_aux_exp_neg_abs_sqrt_pi_integrable
public import Theorems.Thm_Auto_aux_one_sub_sqrtOneMinusGaussian_nonneg
public import Theorems.Thm_Auto_aux_one_sub_sqrtOneMinusGaussian_le_gaussian
public import Theorems.Thm_Auto_aux_sqrtGaussianFrequencyProfile_integrable_real
public import Theorems.Thm_Auto_aux_auxiliaryFunctionB_integrable

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    eLpNorm auxiliaryFunctionB 1 volume ≤ ENNReal.ofReal 6 := by
  have hprofile_bound :
      (∫ x : ℝ, 1 - sqrtOneMinusGaussian x) ≤ ∫ x : ℝ, gaussian x := by
    apply integral_mono aux_sqrtGaussianFrequencyProfile_integrable_real aux_gaussian_integrable
    intro x
    exact aux_one_sub_sqrtOneMinusGaussian_le_gaussian x
  have habel_bound :
      (∫ x : ℝ, Real.exp (-|Real.sqrt Real.pi * x|)) ≤
        ∫ x : ℝ, aux_poissonFrequency x := by
    apply integral_mono aux_exp_neg_abs_sqrt_pi_integrable aux_poissonFrequency_integrable
    intro x
    exact aux_exp_neg_abs_sqrt_pi_le_poissonFrequency x
  have hnorm_bound : (∫ x : ℝ, ‖auxiliaryFunctionB x‖) ≤ 6 := by
    have hsum_integrable : Integrable (fun x : ℝ =>
        (1 - sqrtOneMinusGaussian x) + Real.exp (-|Real.sqrt Real.pi * x|)) :=
      aux_sqrtGaussianFrequencyProfile_integrable_real.add
        aux_exp_neg_abs_sqrt_pi_integrable
    calc
      (∫ x : ℝ, ‖auxiliaryFunctionB x‖) ≤
          ∫ x : ℝ, (1 - sqrtOneMinusGaussian x) +
            Real.exp (-|Real.sqrt Real.pi * x|) := by
        apply integral_mono aux_auxiliaryFunctionB_integrable.norm hsum_integrable
        intro x
        unfold auxiliaryFunctionB
        calc
          |1 - sqrtOneMinusGaussian x - Real.exp (-|Real.sqrt Real.pi * x|)| ≤
              |1 - sqrtOneMinusGaussian x| + |Real.exp (-|Real.sqrt Real.pi * x|)| :=
            by
              simpa using
                (abs_sub_le (1 - sqrtOneMinusGaussian x) 0
                  (Real.exp (-|Real.sqrt Real.pi * x|)))
          _ = (1 - sqrtOneMinusGaussian x) + Real.exp (-|Real.sqrt Real.pi * x|) := by
            rw [abs_of_nonneg (aux_one_sub_sqrtOneMinusGaussian_nonneg x),
              abs_of_nonneg (Real.exp_pos _).le]
      _ = (∫ x : ℝ, 1 - sqrtOneMinusGaussian x) +
          ∫ x : ℝ, Real.exp (-|Real.sqrt Real.pi * x|) := by
        rw [integral_add aux_sqrtGaussianFrequencyProfile_integrable_real
          aux_exp_neg_abs_sqrt_pi_integrable]
      _ ≤ (∫ x : ℝ, gaussian x) + ∫ x : ℝ, aux_poissonFrequency x := by
        exact add_le_add hprofile_bound habel_bound
      _ = (3 : ℝ) := by
        rw [aux_integral_gaussian, aux_integral_poissonFrequency]
        norm_num
      _ ≤ (6 : ℝ) := by norm_num
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm aux_auxiliaryFunctionB_integrable]
  exact ENNReal.ofReal_le_ofReal hnorm_bound
end Auto
