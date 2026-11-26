-- Prove2me | solution 1 for Auto.aux_gaussian_le_four_bracket_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:38.177521+00:00
-- url     : https://prove2.me/submissions/982f8244-3579-434d-8b49-66e30f63c79d

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
public import Theorems.Thm_Auto_aux_gaussian_le_one

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    gaussian x ≤ 4 * bracketBump x ^ 2 := by
  rw [bracketBump]
  have hden : 0 < (1 + |x|) ^ 2 := sq_pos_of_pos (by positivity)
  have hrewrite : 4 * (1 + |x|)⁻¹ ^ 2 = 4 / (1 + |x|) ^ 2 := by
    field_simp
  rw [hrewrite]
  by_cases hx : |x| ≤ 1
  · calc
      gaussian x ≤ 1 := aux_gaussian_le_one x
      _ ≤ 4 / (1 + |x|) ^ 2 := by
        apply (le_div_iff₀ hden).2
        have hbase : 1 + |x| ≤ (2 : ℝ) := by linarith
        have hsquare : (1 + |x|) ^ 2 ≤ (2 : ℝ) ^ 2 :=
          (sq_le_sq₀ (by positivity) (by norm_num)).2 hbase
        norm_num at hsquare
        nlinarith
  · have hx' : 1 ≤ |x| := le_of_not_ge hx
    have hApos : 0 < 1 + Real.pi * x ^ 2 := by positivity
    have hexp : 1 + Real.pi * x ^ 2 ≤ Real.exp (Real.pi * x ^ 2) := by
      simpa [add_comm] using Real.add_one_le_exp (Real.pi * x ^ 2)
    have hinv : Real.exp (-Real.pi * x ^ 2) ≤ (1 + Real.pi * x ^ 2)⁻¹ := by
      rw [show -Real.pi * x ^ 2 = -(Real.pi * x ^ 2) by ring, Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos _) hApos).2 hexp
    calc
      gaussian x = Real.exp (-Real.pi * x ^ 2) := rfl
      _ ≤ (1 + Real.pi * x ^ 2)⁻¹ := hinv
      _ ≤ 4 / (1 + |x|) ^ 2 := by
        have hrewrite' : 4 / (1 + |x|) ^ 2 = ((1 + |x|) ^ 2 / 4)⁻¹ := by
          field_simp
        rw [hrewrite']
        apply (inv_le_inv₀ hApos (by positivity)).2
        rw [← sq_abs x]
        have hquad : (1 + |x|) ^ 2 ≤ 4 * |x| ^ 2 := by
          nlinarith [sq_nonneg (|x| - 1)]
        have hpi : 3 * |x| ^ 2 ≤ Real.pi * |x| ^ 2 :=
          mul_le_mul_of_nonneg_right (le_of_lt Real.pi_gt_three) (sq_nonneg _)
        nlinarith
end Auto
