-- Prove2me | solution 1 for Auto.aux_sqrtOneMinusGaussian_half_of_half_le_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:03.102105+00:00
-- url     : https://prove2.me/submissions/abe00c2a-1cac-4ca5-af56-d0c20cd139b6

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
theorem _root_.solution {x : ℝ}
    (hx : 1 / 2 ≤ |x|) :
    1 / 2 ≤ sqrtOneMinusGaussian x := by
  have hx2 : 1 / 4 ≤ x ^ 2 := by
    have h := sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (abs_nonneg x)
    have h' := h.mpr hx
    rw [sq_abs] at h'
    norm_num at h' ⊢
    exact h'
  have hu : 1 / 3 ≤ Real.pi * x ^ 2 := by
    calc
      (1 / 3 : ℝ) ≤ 3 * (1 / 4) := by norm_num
      _ ≤ Real.pi * x ^ 2 := by
        nlinarith [Real.pi_gt_three,
          mul_le_mul_of_nonneg_left hx2 Real.pi_pos.le,
          mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg x)]
  have hrecip : gaussian x ≤ (1 + Real.pi * x ^ 2)⁻¹ := by
    change Real.exp (-Real.pi * x ^ 2) ≤ (1 + Real.pi * x ^ 2)⁻¹
    rw [show -Real.pi * x ^ 2 = -(Real.pi * x ^ 2) by ring, Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2
      (by simpa [add_comm] using Real.add_one_le_exp (Real.pi * x ^ 2))
  have hgauss : gaussian x ≤ 3 / 4 := by
    calc
      gaussian x ≤ (1 + Real.pi * x ^ 2)⁻¹ := hrecip
      _ ≤ (1 + 1 / 3)⁻¹ :=
        (inv_le_inv₀ (by positivity) (by positivity)).2 (by linarith)
      _ = 3 / 4 := by norm_num
  apply le_of_sq_le_sq ?_ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (aux_one_sub_gaussian_nonneg x)]
  linarith
end Auto
