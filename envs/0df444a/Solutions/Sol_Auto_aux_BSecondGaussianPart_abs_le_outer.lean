-- Prove2me | solution 1 for Auto.aux_BSecondGaussianPart_abs_le_outer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:00:05.384941+00:00
-- url     : https://prove2.me/submissions/57445681-e8e3-4a24-b41d-65f4a2b64619

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
public import Theorems.Thm_Auto_aux_sqrtOneMinusGaussian_pos
public import Theorems.Thm_Auto_aux_sqrtOneMinusGaussian_lower
public import Theorems.Thm_Auto_aux_abs_mul_exp_neg_pi_half_sq_le
public import Theorems.Thm_Auto_aux_two_pi_sqrt_pi_le_twelve

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
      12 * Real.exp (-(1 / 2) * x ^ 2) +
        8 * Real.exp (-(Real.pi / 2) * x ^ 2) := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  let q : ℝ := Real.exp (-(Real.pi / 2) * x ^ 2)
  let L : ℝ := Real.sqrt Real.pi * |x| * q
  let A : ℝ := 2 * Real.pi * Real.sqrt Real.pi * |x| * q +
    2 * Real.sqrt Real.pi * q
  let B : ℝ := 2 * Real.sqrt Real.pi * q
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hL : L ≤ sqrtOneMinusGaussian x := by
    dsimp [L, q]
    convert aux_sqrtOneMinusGaussian_lower x using 1
  have hLpos : 0 < L := by
    dsimp [L, q]
    exact mul_pos (mul_pos (Real.sqrt_pos.2 Real.pi_pos) (abs_pos.mpr hx0))
      (Real.exp_pos _)
  have hfpos : 0 < sqrtOneMinusGaussian x :=
    aux_sqrtOneMinusGaussian_pos hx0
  have hgaussian : gaussian x = q ^ 2 := by
    dsimp [q]
    change Real.exp (-Real.pi * x ^ 2) =
      Real.exp (-(Real.pi / 2) * x ^ 2) ^ 2
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsqrtsq : Real.sqrt Real.pi ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  have hbase : 0 ≤ 2 * |x| - 1 := by linarith
  have hAnonneg : 0 ≤ A := by
    dsimp [A, q]
    positivity
  have hBnonneg : 0 ≤ B := by
    dsimp [B, q]
    positivity
  have hcoef :
      |4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| ≤
        4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi := by
    calc
      |4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| ≤
          |4 * Real.pi ^ 2 * x ^ 2| + |2 * Real.pi| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (4 * Real.pi ^ 2 * x ^ 2) 0 (2 * Real.pi))
      _ = 4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have hAcore :
      (4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi) * gaussian x ≤ A * (2 * L) := by
    rw [hgaussian]
    have hnonneg : 0 ≤ 2 * Real.pi * q ^ 2 * (2 * |x| - 1) :=
      mul_nonneg (mul_nonneg (by positivity) (sq_nonneg q)) hbase
    calc
      (4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi) * q ^ 2 ≤
          (4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi) * q ^ 2 +
            2 * Real.pi * q ^ 2 * (2 * |x| - 1) :=
        le_add_of_nonneg_right hnonneg
      _ = 4 * Real.pi ^ 2 * x ^ 2 * q ^ 2 +
          4 * Real.pi * |x| * q ^ 2 := by ring
      _ = A * (2 * L) := by
        symm
        calc
          A * (2 * L) =
              4 * Real.pi * (Real.sqrt Real.pi) ^ 2 * |x| ^ 2 * q ^ 2 +
                4 * (Real.sqrt Real.pi) ^ 2 * |x| * q ^ 2 := by
            dsimp [A, L]
            ring
          _ = 4 * Real.pi ^ 2 * x ^ 2 * q ^ 2 +
                4 * Real.pi * |x| * q ^ 2 := by
            rw [hsqrtsq, sq_abs]
            ring
  have hA :
      |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x)| ≤ A := by
    have hden : 0 < 2 * sqrtOneMinusGaussian x := by positivity
    calc
      |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x)| =
          |4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| * gaussian x /
            (2 * sqrtOneMinusGaussian x) := by
        rw [abs_div, abs_mul, abs_of_pos (aux_gaussian_pos x), abs_of_pos hden]
      _ ≤ A := (div_le_iff₀ hden).2 <| by
        calc
          |4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| * gaussian x ≤
              (4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi) * gaussian x :=
            mul_le_mul_of_nonneg_right hcoef (aux_gaussian_pos x).le
          _ ≤ A * (2 * L) := hAcore
          _ ≤ A * (2 * sqrtOneMinusGaussian x) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hL (by norm_num)) hAnonneg
  have hLcube : L ^ 3 ≤ sqrtOneMinusGaussian x ^ 3 :=
    pow_le_pow_left₀ hLpos.le hL 3
  have hBcore :
      (-2 * Real.pi * x * gaussian x) ^ 2 ≤ B * (4 * L ^ 3) := by
    rw [hgaussian]
    have hnonneg :
        0 ≤ 4 * Real.pi ^ 2 * |x| ^ 2 * q ^ 4 * (2 * |x| - 1) := by
      have h4 : (0 : ℝ) ≤ 4 := by norm_num
      have hp2 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
      have hx2 : 0 ≤ |x| ^ 2 := sq_nonneg _
      have hq4 : 0 ≤ q ^ 4 := pow_nonneg hqpos.le _
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h4 hp2) hx2) hq4) hbase
    calc
      (-2 * Real.pi * x * q ^ 2) ^ 2 =
          4 * Real.pi ^ 2 * x ^ 2 * q ^ 4 := by ring
      _ ≤ 4 * Real.pi ^ 2 * x ^ 2 * q ^ 4 +
            4 * Real.pi ^ 2 * |x| ^ 2 * q ^ 4 * (2 * |x| - 1) :=
        le_add_of_nonneg_right hnonneg
      _ = 8 * Real.pi ^ 2 * |x| ^ 3 * q ^ 4 := by
        rw [show x ^ 2 = |x| ^ 2 by rw [sq_abs]]
        ring
      _ = B * (4 * L ^ 3) := by
        symm
        calc
          B * (4 * L ^ 3) =
              8 * (Real.sqrt Real.pi) ^ 4 * |x| ^ 3 * q ^ 4 := by
            dsimp [B, L]
            ring
          _ = 8 * Real.pi ^ 2 * |x| ^ 3 * q ^ 4 := by
            rw [show Real.sqrt Real.pi ^ 4 =
              (Real.sqrt Real.pi ^ 2) ^ 2 by ring, hsqrtsq]
  have hB :
      |(-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)| ≤ B := by
    have hden : 0 < 4 * sqrtOneMinusGaussian x ^ 3 := by positivity
    calc
      |(-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)| =
          (-2 * Real.pi * x * gaussian x) ^ 2 /
            (4 * sqrtOneMinusGaussian x ^ 3) := by
        rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos hden]
      _ ≤ B := (div_le_iff₀ hden).2 <| by
        calc
          (-2 * Real.pi * x * gaussian x) ^ 2 ≤ B * (4 * L ^ 3) := hBcore
          _ ≤ B * (4 * sqrtOneMinusGaussian x ^ 3) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hLcube (by norm_num)) hBnonneg
  have hsqrtle : Real.sqrt Real.pi ≤ 2 := by
    nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi,
      Real.pi_le_four]
  have hfirst :
      2 * Real.pi * Real.sqrt Real.pi * |x| * q ≤
        12 * Real.exp (-(1 / 2) * x ^ 2) := by
    calc
      2 * Real.pi * Real.sqrt Real.pi * |x| * q =
          (2 * Real.pi * Real.sqrt Real.pi) * (|x| * q) := by ring
      _ ≤ 12 * (|x| * q) :=
        mul_le_mul_of_nonneg_right aux_two_pi_sqrt_pi_le_twelve
          (mul_nonneg (abs_nonneg x) hqpos.le)
      _ ≤ 12 * Real.exp (-(1 / 2) * x ^ 2) :=
        mul_le_mul_of_nonneg_left (aux_abs_mul_exp_neg_pi_half_sq_le x) (by norm_num)
  have hsecond : 4 * Real.sqrt Real.pi * q ≤ 8 * q := by
    calc
      4 * Real.sqrt Real.pi * q ≤ (4 * 2) * q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrtle (by norm_num)) hqpos.le
      _ = 8 * q := by ring
  calc
    |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)| ≤
        |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x)| +
          |(-2 * Real.pi * x * gaussian x) ^ 2 /
            (4 * sqrtOneMinusGaussian x ^ 3)| := abs_add_le _ _
    _ ≤ A + B := add_le_add hA hB
    _ = 2 * Real.pi * Real.sqrt Real.pi * |x| * q +
          4 * Real.sqrt Real.pi * q := by
      dsimp [A, B]
      ring
    _ ≤ 12 * Real.exp (-(1 / 2) * x ^ 2) + 8 * q := add_le_add hfirst hsecond
end Auto
