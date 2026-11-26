-- Prove2me | solution 1 for Auto.aux_gaussian_deriv_le_C_gaussianBumpDecay_one_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:51.869111+00:00
-- url     : https://prove2.me/submissions/84758dc0-a052-4c33-916b-fa6d7a487cab

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
public import Theorems.Thm_Auto_aux_gaussian_le_sixteen_bracket_four

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    |-2 * Real.pi * x * gaussian x| ≤
      C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 := by
  have hbracket : |x| * bracketBump x ^ 4 ≤ bracketBump x ^ 2 := by
    rw [bracketBump]
    have hden : 0 < 1 + |x| := by positivity
    have habs : |x| ≤ (1 + |x|) ^ 2 := by
      nlinarith [abs_nonneg x]
    calc
      |x| * (1 + |x|)⁻¹ ^ 4 ≤
          (1 + |x|) ^ 2 * (1 + |x|)⁻¹ ^ 4 :=
        mul_le_mul_of_nonneg_right habs (by positivity)
      _ = (1 + |x|)⁻¹ ^ 2 := by
        field_simp [ne_of_gt hden]
  have hconstant : 32 * Real.pi ≤ C_gaussianBumpDecay 1 2 := by
    have hpi : 32 * Real.pi ≤ 504 / 5 := by
      nlinarith [Real.pi_lt_d2]
    have hsquare : (Real.sqrt (76 : ℝ)) ^ 2 = 76 :=
      Real.sq_sqrt (by norm_num)
    have hsqrtnonneg : 0 ≤ Real.sqrt (76 : ℝ) := Real.sqrt_nonneg _
    have hsqrt : (17 / 2 : ℝ) ≤ Real.sqrt 76 := by
      nlinarith
    calc
      32 * Real.pi ≤ 504 / 5 := hpi
      _ ≤ Real.sqrt 76 * 12 := by nlinarith
      _ = C_gaussianBumpDecay 1 2 := by
        norm_num [C_gaussianBumpDecay, Real.sqrt_eq_rpow]
  have hfactor : 0 ≤ 2 * Real.pi * |x| := by positivity
  calc
    |-2 * Real.pi * x * gaussian x| = 2 * Real.pi * |x| * gaussian x := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg Real.pi_pos.le,
        abs_of_nonneg (aux_gaussian_pos x).le]
    _ ≤ 2 * Real.pi * |x| * (16 * bracketBump x ^ 4) :=
      mul_le_mul_of_nonneg_left (aux_gaussian_le_sixteen_bracket_four x) hfactor
    _ = (32 * Real.pi) * (|x| * bracketBump x ^ 4) := by ring
    _ ≤ (32 * Real.pi) * bracketBump x ^ 2 :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ ≤ C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)
end Auto
