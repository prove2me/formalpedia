-- Prove2me | solution 1 for Auto.aux_norm_inverseFourier_auxiliaryFunctionB_le_fifteen_bracket_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:56.469524+00:00
-- url     : https://prove2.me/submissions/15168ff4-d416-4f70-8ec5-fe468c671fe6

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
public import Theorems.Thm_Auto_aux_norm_inverseFourier_auxiliaryFunctionB_le_six
public import Theorems.Thm_Auto_aux_quadratic_inverseFourier_auxiliaryFunctionB_bound

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ ≤
      15 * bracketBump x ^ 2 := by
  rw [bracketBump]
  have hden : 0 < (1 + |x|) ^ 2 := sq_pos_of_pos (by positivity)
  have hrewrite : 15 * (1 + |x|)⁻¹ ^ 2 = 15 / (1 + |x|) ^ 2 := by
    field_simp
  rw [hrewrite]
  by_cases hx : |x| ≤ 5 / 9
  · apply (le_div_iff₀ hden).2
    have hsmall := aux_norm_inverseFourier_auxiliaryFunctionB_le_six x
    have hfactor : (1 + |x|) ^ 2 ≤ (14 / 9 : ℝ) ^ 2 := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).2
      linarith
    calc
      ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ *
          (1 + |x|) ^ 2 ≤ 6 * (1 + |x|) ^ 2 :=
        mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)
      _ ≤ 6 * (14 / 9 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hfactor (by norm_num)
      _ ≤ 15 := by norm_num
  · have hx' : 5 / 9 ≤ |x| := le_of_not_ge hx
    apply (le_div_iff₀ hden).2
    have hquad := aux_quadratic_inverseFourier_auxiliaryFunctionB_bound x
    have hsum : 1 + |x| ≤ (14 / 5 : ℝ) * |x| := by linarith
    have hbase : (1 + |x|) ^ 2 ≤ (14 / 5 : ℝ) ^ 2 * x ^ 2 := by
      calc
        (1 + |x|) ^ 2 ≤ ((14 / 5 : ℝ) * |x|) ^ 2 :=
          (sq_le_sq₀ (by positivity) (by positivity)).2 hsum
        _ = (14 / 5 : ℝ) ^ 2 * x ^ 2 := by rw [mul_pow, sq_abs]
    have hpiSq : 9 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hcoeff : (196 / 25 : ℝ) ≤ (49 / 225 : ℝ) * (4 * Real.pi ^ 2) := by
      nlinarith
    have hfactor : (1 + |x|) ^ 2 ≤
        (49 / 225 : ℝ) * (4 * Real.pi ^ 2 * x ^ 2) := by
      calc
        (1 + |x|) ^ 2 ≤ (14 / 5 : ℝ) ^ 2 * x ^ 2 := hbase
        _ = (196 / 25 : ℝ) * x ^ 2 := by norm_num
        _ ≤ ((49 / 225 : ℝ) * (4 * Real.pi ^ 2)) * x ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
        _ = (49 / 225 : ℝ) * (4 * Real.pi ^ 2 * x ^ 2) := by ring
    calc
      ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ *
          (1 + |x|) ^ 2 ≤
          ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ *
            ((49 / 225 : ℝ) * (4 * Real.pi ^ 2 * x ^ 2)) :=
        mul_le_mul_of_nonneg_left hfactor (norm_nonneg _)
      _ = (49 / 225 : ℝ) * ((4 * Real.pi ^ 2 * x ^ 2) *
          ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖) := by
        ring
      _ ≤ (49 / 225 : ℝ) * 56 :=
        mul_le_mul_of_nonneg_left hquad (by norm_num)
      _ ≤ 15 := by norm_num
end Auto
