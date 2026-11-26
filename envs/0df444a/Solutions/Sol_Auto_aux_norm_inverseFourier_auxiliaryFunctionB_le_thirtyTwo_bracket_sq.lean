-- Prove2me | solution 1 for Auto.aux_norm_inverseFourier_auxiliaryFunctionB_le_thirtyTwo_bracket_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:54.79439+00:00
-- url     : https://prove2.me/submissions/e02901ba-fd4f-490b-82cd-4fdd3da4b944

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
public import Theorems.Thm_Auto_aux_norm_inverseFourier_auxiliaryFunctionB_le_eight
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
      32 * bracketBump x ^ 2 := by
  rw [bracketBump]
  have hden : 0 < (1 + |x|) ^ 2 := sq_pos_of_pos (by positivity)
  have hrewrite : 32 * (1 + |x|)⁻¹ ^ 2 = 32 / (1 + |x|) ^ 2 := by
    field_simp
  rw [hrewrite]
  by_cases hx : |x| ≤ 1
  · apply (le_div_iff₀ hden).2
    have hsmall := aux_norm_inverseFourier_auxiliaryFunctionB_le_eight x
    have hfactor : (1 + |x|) ^ 2 ≤ 4 := by
      calc
        (1 + |x|) ^ 2 ≤ (2 : ℝ) ^ 2 :=
          (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
        _ = 4 := by norm_num
    calc
      ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ *
          (1 + |x|) ^ 2 ≤ 8 * (1 + |x|) ^ 2 :=
        mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)
      _ ≤ 8 * 4 := mul_le_mul_of_nonneg_left hfactor (by norm_num)
      _ = 32 := by norm_num
  · have hx' : 1 ≤ |x| := le_of_not_ge hx
    apply (le_div_iff₀ hden).2
    have hquad := aux_quadratic_inverseFourier_auxiliaryFunctionB_bound x
    have hsum : 1 + |x| ≤ 2 * |x| := by linarith
    have hfactor : (1 + |x|) ^ 2 ≤ (8 / 25 : ℝ) * (4 * Real.pi ^ 2 * x ^ 2) := by
      have hbase : (1 + |x|) ^ 2 ≤ 4 * x ^ 2 := by
        calc
          (1 + |x|) ^ 2 ≤ (2 * |x|) ^ 2 :=
            (sq_le_sq₀ (by positivity) (by positivity)).mpr hsum
          _ = 4 * x ^ 2 := by
            rw [show (2 * |x|) ^ 2 = 4 * |x| ^ 2 by ring, sq_abs]
      calc
        (1 + |x|) ^ 2 ≤ 4 * x ^ 2 := hbase
        _ ≤ (32 / 25 : ℝ) * Real.pi ^ 2 * x ^ 2 := by
          gcongr
          nlinarith [Real.pi_gt_three]
        _ = (8 / 25 : ℝ) * (4 * Real.pi ^ 2 * x ^ 2) := by ring
    calc
      ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ *
          (1 + |x|) ^ 2 ≤
          ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ *
            ((8 / 25 : ℝ) * (4 * Real.pi ^ 2 * x ^ 2)) :=
        mul_le_mul_of_nonneg_left hfactor (norm_nonneg _)
      _ = (8 / 25 : ℝ) * ((4 * Real.pi ^ 2 * x ^ 2) *
          ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖) := by ring
      _ ≤ (8 / 25 : ℝ) * 56 := mul_le_mul_of_nonneg_left hquad (by norm_num)
      _ ≤ 32 := by norm_num
end Auto
