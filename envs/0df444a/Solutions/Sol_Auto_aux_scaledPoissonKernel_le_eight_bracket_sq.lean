-- Prove2me | solution 1 for Auto.aux_scaledPoissonKernel_le_eight_bracket_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:04:56.460143+00:00
-- url     : https://prove2.me/submissions/27728545-bdf8-4045-bf6f-eb88c8711ac0

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
    aux_scaledPoissonKernel x ≤ 8 * bracketBump x ^ 2 := by
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
  have hsqrtSq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hsqrtge : 1 ≤ Real.sqrt Real.pi := by nlinarith [Real.pi_gt_three]
  have hcoef : 2 / Real.sqrt Real.pi ≤ 2 := by
    apply (div_le_iff₀ hsqrtpos).2
    nlinarith
  have hden : 1 + x ^ 2 ≤ 1 + 4 * Real.pi * x ^ 2 := by
    have hpi : 1 ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_le_mul_of_nonneg_right hpi (sq_nonneg x)]
  have hdenpos : 0 < 1 + x ^ 2 := by positivity
  have hdenScaledPos : 0 < 1 + 4 * Real.pi * x ^ 2 := by positivity
  have hinv : (1 + 4 * Real.pi * x ^ 2)⁻¹ ≤ (1 + x ^ 2)⁻¹ := by
    exact (inv_le_inv₀ hdenScaledPos hdenpos).2 hden
  have hbracketden : (1 + |x|) ^ 2 ≤ 4 * (1 + x ^ 2) := by
    calc
      (1 + |x|) ^ 2 ≤ 4 * (1 + |x| ^ 2) := by
        nlinarith [sq_nonneg (|x| - 1)]
      _ = 4 * (1 + x ^ 2) := by rw [sq_abs]
  have hbracketpos : 0 < (1 + |x|) ^ 2 := sq_pos_of_pos (by positivity)
  have hlast : 2 * (1 + x ^ 2)⁻¹ ≤ 8 * (1 + |x|)⁻¹ ^ 2 := by
    have hleft : 2 * (1 + x ^ 2)⁻¹ = 2 / (1 + x ^ 2) := by field_simp
    have hright : 8 * (1 + |x|)⁻¹ ^ 2 = 8 / (1 + |x|) ^ 2 := by field_simp
    rw [hleft, hright]
    apply (div_le_div_iff₀ hdenpos hbracketpos).2
    nlinarith
  calc
    (2 / Real.sqrt Real.pi) * (1 + 4 * Real.pi * x ^ 2)⁻¹ ≤
        2 * (1 + 4 * Real.pi * x ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hcoef (inv_nonneg.mpr hdenScaledPos.le)
    _ ≤ 2 * (1 + x ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ ≤ 8 * (1 + |x|)⁻¹ ^ 2 := hlast
end Auto
