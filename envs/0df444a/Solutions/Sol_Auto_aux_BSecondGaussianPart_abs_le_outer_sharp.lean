-- Prove2me | solution 1 for Auto.aux_BSecondGaussianPart_abs_le_outer_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:00:11.920058+00:00
-- url     : https://prove2.me/submissions/7860892c-bfb2-46d4-953b-b27346d957e2

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
public import Theorems.Thm_Auto_aux_sqrtOneMinusGaussian_half_of_half_le_abs

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
    |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)| ≤
      2 * Real.pi * gaussian x + 12 * Real.pi ^ 2 * x ^ 2 * gaussian x := by
  let s := sqrtOneMinusGaussian x
  have hs : 1 / 2 ≤ s := aux_sqrtOneMinusGaussian_half_of_half_le_abs hx
  have hspos : 0 < s := by linarith
  have hgauss_nonneg : 0 ≤ gaussian x := (aux_gaussian_pos x).le
  have hgauss_le_one : gaussian x ≤ 1 := by
    change Real.exp (-Real.pi * x ^ 2) ≤ 1
    exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg x])
  have hcoef : |4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| ≤
      4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi := by
    calc
      |4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| ≤
          |4 * Real.pi ^ 2 * x ^ 2| + |2 * Real.pi| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (4 * Real.pi ^ 2 * x ^ 2) 0 (2 * Real.pi))
      _ = 4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have hfirst :
      |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * s)| ≤ 2 * Real.pi * gaussian x + 4 * Real.pi ^ 2 * x ^ 2 * gaussian x := by
    have hden : 0 < 2 * s := by positivity
    calc
      |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
            (2 * s)| =
          |4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| * gaussian x / (2 * s) := by
            rw [abs_div, abs_mul, abs_of_nonneg hgauss_nonneg, abs_of_pos hden]
      _ ≤ |4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| * gaussian x := by
        apply (div_le_iff₀ hden).2
        have hscale : 1 ≤ 2 * s := by linarith
        calc
          |4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| * gaussian x =
              (|4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| * gaussian x) * 1 := by ring
          _ ≤ (|4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| * gaussian x) * (2 * s) :=
            mul_le_mul_of_nonneg_left hscale
              (mul_nonneg (abs_nonneg _) hgauss_nonneg)
      _ ≤ (4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi) * gaussian x :=
        mul_le_mul_of_nonneg_right hcoef hgauss_nonneg
      _ = 2 * Real.pi * gaussian x + 4 * Real.pi ^ 2 * x ^ 2 * gaussian x := by ring
  have hs3 : (1 / 2 : ℝ) ^ 3 ≤ s ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hs 3
  have hden3 : 1 / 2 ≤ 4 * s ^ 3 := by nlinarith
  have hsecond :
      |(-2 * Real.pi * x * gaussian x) ^ 2 / (4 * s ^ 3)| ≤
        8 * Real.pi ^ 2 * x ^ 2 * gaussian x := by
    have hden : 0 < 4 * s ^ 3 := by positivity
    have hinv : (4 * s ^ 3)⁻¹ ≤ 2 := by
      apply (inv_le_iff_one_le_mul₀ hden).2
      nlinarith
    calc
      |(-2 * Real.pi * x * gaussian x) ^ 2 / (4 * s ^ 3)| =
          (-2 * Real.pi * x * gaussian x) ^ 2 * (4 * s ^ 3)⁻¹ := by
        rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos hden, div_eq_mul_inv]
      _ ≤ (-2 * Real.pi * x * gaussian x) ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
      _ = 8 * Real.pi ^ 2 * x ^ 2 * gaussian x ^ 2 := by ring
      _ ≤ 8 * Real.pi ^ 2 * x ^ 2 * gaussian x := by
        gcongr
        simpa [pow_two] using mul_le_of_le_one_right hgauss_nonneg hgauss_le_one
  change |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * s) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * s ^ 3)| ≤ _
  calc
    |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * s) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * s ^ 3)| ≤
        |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * s)| + |(-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * s ^ 3)| := abs_add_le _ _
    _ ≤ (2 * Real.pi * gaussian x + 4 * Real.pi ^ 2 * x ^ 2 * gaussian x) +
          8 * Real.pi ^ 2 * x ^ 2 * gaussian x := add_le_add hfirst hsecond
    _ = 2 * Real.pi * gaussian x + 12 * Real.pi ^ 2 * x ^ 2 * gaussian x := by ring
end Auto
