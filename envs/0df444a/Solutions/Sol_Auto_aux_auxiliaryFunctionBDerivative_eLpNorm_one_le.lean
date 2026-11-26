-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBDerivative_eLpNorm_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:04:06.041444+00:00
-- url     : https://prove2.me/submissions/1901242d-cfaa-41e7-ac6c-d21811c051da

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
public import Theorems.Thm_Auto_aux_poissonFrequency_integrable
public import Theorems.Thm_Auto_aux_integral_poissonFrequency
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_norm_le
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_integrable

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    eLpNorm auxiliaryFunctionBDerivative 1 volume ≤ ENNReal.ofReal 12 := by
  have hgaussian : Integrable (fun x : ℝ =>
      Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)) := by
    simpa using
      (integrable_exp_neg_mul_sq (by positivity : 0 < Real.pi / 2)).const_mul
        (Real.sqrt Real.pi)
  have habel : Integrable (fun x : ℝ =>
      Real.sqrt Real.pi * aux_poissonFrequency x) := by
    simpa using aux_poissonFrequency_integrable.const_mul (Real.sqrt Real.pi)
  have hmajorant : Integrable (fun x : ℝ =>
      Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.sqrt Real.pi * aux_poissonFrequency x) := hgaussian.add habel
  have hgaussian_integral :
      (∫ x : ℝ, Real.exp (-(Real.pi / 2) * x ^ 2)) = Real.sqrt 2 := by
    calc
      (∫ x : ℝ, Real.exp (-(Real.pi / 2) * x ^ 2)) =
          Real.sqrt (Real.pi / (Real.pi / 2)) := by
        simpa using (integral_gaussian (Real.pi / 2))
      _ = Real.sqrt 2 := by
        congr 1
        field_simp [Real.pi_ne_zero]
  have hnorm_bound : (∫ x : ℝ, ‖auxiliaryFunctionBDerivative x‖) ≤ 12 := by
    calc
      (∫ x : ℝ, ‖auxiliaryFunctionBDerivative x‖) ≤
          ∫ x : ℝ, Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) +
            Real.sqrt Real.pi * aux_poissonFrequency x := by
        apply integral_mono aux_auxiliaryFunctionBDerivative_integrable.norm hmajorant
        intro x
        exact aux_auxiliaryFunctionBDerivative_norm_le x
      _ = (∫ x : ℝ, Real.sqrt Real.pi *
            Real.exp (-(Real.pi / 2) * x ^ 2)) +
          ∫ x : ℝ, Real.sqrt Real.pi * aux_poissonFrequency x :=
        integral_add hgaussian habel
      _ = Real.sqrt Real.pi * Real.sqrt 2 + Real.sqrt Real.pi * 2 := by
        rw [integral_const_mul, hgaussian_integral,
          integral_const_mul, aux_integral_poissonFrequency]
      _ ≤ 12 := by
        have hsqrtpi_le : Real.sqrt Real.pi ≤ 2 := by
          nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi,
            Real.pi_le_four]
        have hsqrttwo_le : Real.sqrt 2 ≤ 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
            Real.sqrt_nonneg (2 : ℝ)]
        have hprod' : Real.sqrt Real.pi * Real.sqrt 2 ≤ (2 : ℝ) * 2 :=
          mul_le_mul hsqrtpi_le hsqrttwo_le (Real.sqrt_nonneg _) (by norm_num)
        norm_num at hprod'
        have hprod : Real.sqrt Real.pi * Real.sqrt 2 ≤ 4 := hprod'
        have htwice : Real.sqrt Real.pi * 2 ≤ 4 := by nlinarith
        nlinarith
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm aux_auxiliaryFunctionBDerivative_integrable]
  exact ENNReal.ofReal_le_ofReal hnorm_bound
end Auto
