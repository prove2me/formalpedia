-- Prove2me | solution 1 for Auto.aux_BSecondSharpMajorant_integral_le_fiftySix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:01.46532+00:00
-- url     : https://prove2.me/submissions/b925c244-4dec-4e22-9897-7e6d63e9ed7b

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
public import Theorems.Thm_Auto_aux_exp_neg_abs_sqrt_pi_integrable
public import Theorems.Thm_Auto_aux_sq_mul_gaussian_integrable
public import Theorems.Thm_Auto_aux_integral_gaussian_second_moment
public import Theorems.Thm_Auto_aux_integral_exp_neg_abs_sqrt_pi
public import Theorems.Thm_Auto_aux_integral_indicator_localOne

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    (∫ x : ℝ,
      26 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        2 * Real.pi * gaussian x + 12 * Real.pi ^ 2 * x ^ 2 * gaussian x +
          Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)) ≤ 56 := by
  have hlocal : Integrable ((Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun _ : ℝ => (1 : ℝ))) :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
      measurableSet_Icc
  have hlocalMul : Integrable (fun x : ℝ =>
      26 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x) := by
    exact hlocal.const_mul 26
  have hgaussianMul : Integrable (fun x : ℝ => 2 * Real.pi * gaussian x) := by
    exact aux_gaussian_integrable.const_mul (2 * Real.pi)
  have hmomentMul : Integrable (fun x : ℝ =>
      12 * Real.pi ^ 2 * x ^ 2 * gaussian x) := by
    have h := aux_sq_mul_gaussian_integrable.const_mul (12 * Real.pi ^ 2)
    refine h.congr ?_
    filter_upwards [] with x
    ring
  have habelMul : Integrable (fun x : ℝ =>
      Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)) := by
    exact aux_exp_neg_abs_sqrt_pi_integrable.const_mul Real.pi
  have hlocalGaussian : Integrable (fun x : ℝ =>
      26 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        2 * Real.pi * gaussian x) := by
    have h := hlocalMul.add hgaussianMul
    refine h.congr ?_
    filter_upwards [] with x
    simp only [Pi.add_apply]
  have hlocalGaussianMoment : Integrable (fun x : ℝ =>
      26 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        2 * Real.pi * gaussian x + 12 * Real.pi ^ 2 * x ^ 2 * gaussian x) := by
    have h := hlocalGaussian.add hmomentMul
    refine h.congr ?_
    filter_upwards [] with x
    simp only [Pi.add_apply]
  have hmoment_integral :
      (∫ x : ℝ, 12 * Real.pi ^ 2 * x ^ 2 * gaussian x) =
        12 * Real.pi ^ 2 * (∫ x : ℝ, x ^ 2 * gaussian x) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [integral_add hlocalGaussianMoment habelMul,
    integral_add hlocalGaussian hmomentMul,
    integral_add hlocalMul hgaussianMul,
    integral_const_mul, aux_integral_indicator_localOne,
    integral_const_mul, aux_integral_gaussian,
    hmoment_integral, aux_integral_gaussian_second_moment,
    integral_const_mul, aux_integral_exp_neg_abs_sqrt_pi]
  have hpi : Real.pi ≤ 63 / 20 := by nlinarith [Real.pi_lt_d2]
  have hsqrt : Real.sqrt Real.pi ≤ 9 / 5 := by
    calc
      Real.sqrt Real.pi ≤ Real.sqrt ((9 / 5 : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      _ = 9 / 5 := by rw [Real.sqrt_sq_eq_abs]; norm_num
  have hpine : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hsqrtne : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have hmoment : 12 * Real.pi ^ 2 * (2 * Real.pi)⁻¹ = 6 * Real.pi := by
    field_simp [hpine]
    ring
  have habel : Real.pi * (2 / Real.sqrt Real.pi) = 2 * Real.sqrt Real.pi := by
    field_simp [hsqrtne]
    rw [Real.sq_sqrt Real.pi_pos.le]
  rw [hmoment, habel]
  nlinarith
end Auto
