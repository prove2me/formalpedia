-- Prove2me | solution 1 for Auto.aux_scaledPoissonKernel_le_three_halves_bracket_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:51:38.561973+00:00
-- url     : https://prove2.me/submissions/072f6d14-43db-46ce-a756-475c2325217c

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

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    aux_scaledPoissonKernel x ≤ (3 / 2 : ℝ) * bracketBump x ^ 2 := by
  have hformula : aux_scaledPoissonKernel x =
      (2 / Real.sqrt Real.pi) * (1 + 4 * Real.pi * x ^ 2)⁻¹ := by
    have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
    have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    unfold aux_scaledPoissonKernel poissonKernel
    field_simp
    rw [hsq]
    ring
  rw [hformula, bracketBump]
  have hsqrtpos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsqrtlower : (12 / 7 : ℝ) ≤ Real.sqrt Real.pi := by
    calc
      (12 / 7 : ℝ) = Real.sqrt ((12 / 7 : ℝ) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
        norm_num
      _ ≤ Real.sqrt Real.pi := Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
  have hcoef : 2 / Real.sqrt Real.pi ≤ (7 / 6 : ℝ) := by
    apply (div_le_iff₀ hsqrtpos).2
    nlinarith
  have hbracket : 12 * (1 + |x|) ^ 2 ≤ 13 * (1 + 12 * x ^ 2) := by
    rw [← sq_abs x]
    nlinarith [sq_nonneg (12 * |x| - 1)]
  have hbracket' : (1 + |x|) ^ 2 ≤ (13 / 12 : ℝ) * (1 + 12 * x ^ 2) := by
    nlinarith [hbracket]
  have hpiDen : 1 + 12 * x ^ 2 ≤ 1 + 4 * Real.pi * x ^ 2 := by
    have hmul : 12 * x ^ 2 ≤ 4 * Real.pi * x ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
      nlinarith [Real.pi_gt_three]
    linarith
  have hscaledpos : 0 < 1 + 4 * Real.pi * x ^ 2 := by positivity
  have hbracketpos : 0 < (1 + |x|) ^ 2 := sq_pos_of_pos (by positivity)
  have hleft : (2 / Real.sqrt Real.pi) * (1 + 4 * Real.pi * x ^ 2)⁻¹ =
      (2 / Real.sqrt Real.pi) / (1 + 4 * Real.pi * x ^ 2) := by
    field_simp
  have hright : (3 / 2 : ℝ) * (1 + |x|)⁻¹ ^ 2 =
      (3 / 2 : ℝ) / (1 + |x|) ^ 2 := by
    field_simp
  rw [hleft, hright]
  apply (div_le_div_iff₀ hscaledpos hbracketpos).2
  calc
    (2 / Real.sqrt Real.pi) * (1 + |x|) ^ 2 ≤
        (7 / 6 : ℝ) * (1 + |x|) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ ≤ (7 / 6 : ℝ) * ((13 / 12 : ℝ) * (1 + 12 * x ^ 2)) :=
      mul_le_mul_of_nonneg_left hbracket' (by norm_num)
    _ = ((7 / 6 : ℝ) * (13 / 12 : ℝ)) * (1 + 12 * x ^ 2) := by ring
    _ ≤ (3 / 2 : ℝ) * (1 + 12 * x ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      norm_num
    _ ≤ (3 / 2 : ℝ) * (1 + 4 * Real.pi * x ^ 2) :=
      mul_le_mul_of_nonneg_left hpiDen (by norm_num)
end Auto
