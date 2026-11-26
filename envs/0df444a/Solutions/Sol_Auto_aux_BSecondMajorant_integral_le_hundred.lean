-- Prove2me | solution 1 for Auto.aux_BSecondMajorant_integral_le_hundred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:11:47.194447+00:00
-- url     : https://prove2.me/submissions/f66e5c86-a938-46a4-9691-b47cf259052f

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
public import Theorems.Thm_Auto_aux_integral_indicator_localQuadratic
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
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        12 * Real.exp (-(1 / 2) * x ^ 2) +
        8 * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.pi * aux_poissonFrequency x) ≤ 100 := by
  have hquad : Integrable ((Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun y : ℝ => y ^ 2 + 1 / 4)) :=
    (((continuous_id.pow 2).add continuous_const).continuousOn.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have hone : Integrable ((Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun _ : ℝ => (1 : ℝ))) :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
      measurableSet_Icc
  have hhalf : Integrable (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  have hpi : Integrable (fun x : ℝ => Real.exp (-(Real.pi / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < Real.pi / 2)
  have hquadMul := hquad.const_mul 144
  have honeMul := hone.const_mul 4
  have hhalfMul := hhalf.const_mul 12
  have hpiMul := hpi.const_mul 8
  have hpoissonMul := aux_poissonFrequency_integrable.const_mul Real.pi
  have hquadOne : Integrable (fun x : ℝ =>
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x) := by
    have hsum := hquadMul.add honeMul
    refine hsum.congr ?_
    filter_upwards [] with x
    simp only [Pi.add_apply]
  have hquadOneHalf : Integrable (fun x : ℝ =>
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        12 * Real.exp (-(1 / 2) * x ^ 2)) := by
    have hsum := hquadOne.add hhalfMul
    refine hsum.congr ?_
    filter_upwards [] with x
    simp only [Pi.add_apply]
  have hquadOneHalfPi : Integrable (fun x : ℝ =>
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        12 * Real.exp (-(1 / 2) * x ^ 2) +
        8 * Real.exp (-(Real.pi / 2) * x ^ 2)) := by
    have hsum := hquadOneHalf.add hpiMul
    refine hsum.congr ?_
    filter_upwards [] with x
    simp only [Pi.add_apply]
  have hhalf_integral :
      (∫ x : ℝ, Real.exp (-(1 / 2) * x ^ 2)) = Real.sqrt (2 * Real.pi) := by
    calc
      (∫ x : ℝ, Real.exp (-(1 / 2) * x ^ 2)) =
          Real.sqrt (Real.pi / (1 / 2)) := by
        simpa using (integral_gaussian (1 / 2 : ℝ))
      _ = Real.sqrt (2 * Real.pi) := by
        congr 1
        ring
  have hpi_integral :
      (∫ x : ℝ, Real.exp (-(Real.pi / 2) * x ^ 2)) = Real.sqrt 2 := by
    calc
      (∫ x : ℝ, Real.exp (-(Real.pi / 2) * x ^ 2)) =
          Real.sqrt (Real.pi / (Real.pi / 2)) := by
        simpa using (integral_gaussian (Real.pi / 2))
      _ = Real.sqrt 2 := by
        congr 1
        field_simp [Real.pi_ne_zero]
  have hsqrtTwoPi : Real.sqrt (2 * Real.pi) ≤ 251 / 100 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity),
      Real.sqrt_nonneg (2 * Real.pi), Real.pi_lt_d2]
  have hsqrtTwo : Real.sqrt 2 ≤ 10 / 7 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hpi_bound : Real.pi ≤ 63 / 20 := by
    nlinarith [Real.pi_lt_d2]
  calc
    (∫ x : ℝ,
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        12 * Real.exp (-(1 / 2) * x ^ 2) +
        8 * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.pi * aux_poissonFrequency x) =
        ((144 * (1 / 3) + 4 * 1) + 12 * Real.sqrt (2 * Real.pi)) +
          8 * Real.sqrt 2 + Real.pi * 2 := by
      rw [integral_add hquadOneHalfPi hpoissonMul,
        integral_add hquadOneHalf hpiMul,
        integral_add hquadOne hhalfMul,
        integral_add hquadMul honeMul,
        integral_const_mul, aux_integral_indicator_localQuadratic,
        integral_const_mul, aux_integral_indicator_localOne,
        integral_const_mul, hhalf_integral,
        integral_const_mul, hpi_integral,
        integral_const_mul, aux_integral_poissonFrequency]
    _ ≤ 100 := by
      nlinarith
end Auto
