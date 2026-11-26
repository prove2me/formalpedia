-- Prove2me | solution 1 for Auto.sqrtOneMinusGaussian_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:10:08.075588+00:00
-- url     : https://prove2.me/submissions/9bbc6190-4a8a-42cb-85b8-f07622c93837

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
public import Theorems.Thm_Auto_aux_one_sub_gaussian_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) (hx : |x| ≤ 1 / 2) :
    1 / 2 * |x| ≤ sqrtOneMinusGaussian x := by
  have hx2 : x ^ 2 ≤ 1 / 4 := by
    have h : |x| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg x) (by norm_num)).2 hx
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hpi_sq_nonneg : 0 ≤ Real.pi * x ^ 2 :=
    mul_nonneg Real.pi_pos.le (sq_nonneg x)
  have hden_pos : 0 < 1 + Real.pi * x ^ 2 := by positivity
  have hpi_sq_le : Real.pi * x ^ 2 ≤ 1 := by
    calc
      Real.pi * x ^ 2 ≤ 4 * x ^ 2 := by
        exact mul_le_mul_of_nonneg_right (le_of_lt Real.pi_lt_four) (sq_nonneg x)
      _ ≤ 4 * (1 / 4) := by
        exact mul_le_mul_of_nonneg_left hx2 (by norm_num)
      _ = 1 := by norm_num
  have hden_le : 1 + Real.pi * x ^ 2 ≤ 2 := by linarith
  have hexp : 1 + Real.pi * x ^ 2 ≤ Real.exp (Real.pi * x ^ 2) := by
    simpa [add_comm] using Real.add_one_le_exp (Real.pi * x ^ 2)
  have hrecip : Real.exp (-Real.pi * x ^ 2) ≤ (1 + Real.pi * x ^ 2)⁻¹ := by
    rw [show -Real.pi * x ^ 2 = -(Real.pi * x ^ 2) by ring, Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hden_pos).2 hexp
  have hfrac : x ^ 2 / 4 ≤ 1 - (1 + Real.pi * x ^ 2)⁻¹ := by
    have hid : 1 - (1 + Real.pi * x ^ 2)⁻¹ =
        (Real.pi * x ^ 2) / (1 + Real.pi * x ^ 2) := by
      field_simp
      ring
    rw [hid]
    have hrewrite : x ^ 2 / 4 =
        (x ^ 2 / 4 * (1 + Real.pi * x ^ 2)) / (1 + Real.pi * x ^ 2) := by
      field_simp
    rw [hrewrite]
    apply (div_le_div_iff_of_pos_right hden_pos).2
    calc
      x ^ 2 / 4 * (1 + Real.pi * x ^ 2) ≤ x ^ 2 / 4 * 2 := by
        gcongr
      _ = x ^ 2 / 2 := by ring
      _ ≤ Real.pi * x ^ 2 := by nlinarith [sq_nonneg x, Real.pi_gt_three]
  have hrad : x ^ 2 / 4 ≤ 1 - gaussian x := by
    change x ^ 2 / 4 ≤ 1 - Real.exp (-Real.pi * x ^ 2)
    linarith
  apply le_of_sq_le_sq ?_ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt]
  · calc
      (1 / 2 * |x|) ^ 2 = x ^ 2 / 4 := by
        rw [show (1 / 2 * |x|) ^ 2 = (1 / 2 : ℝ) ^ 2 * |x| ^ 2 by ring, sq_abs]
        ring
      _ ≤ 1 - gaussian x := hrad
  · exact aux_one_sub_gaussian_nonneg x
end Auto
