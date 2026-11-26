-- Prove2me | solution 1 for Auto.aux_gaussian_le_sixteen_bracket_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:45.055314+00:00
-- url     : https://prove2.me/submissions/346de30e-c904-44b6-abb0-6a3e93fd3ad0

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
    gaussian x ≤ 16 * bracketBump x ^ 4 := by
  rw [bracketBump]
  have hden : 0 < (1 + |x|) ^ 4 := pow_pos (by positivity) _
  have hrewrite : 16 * (1 + |x|)⁻¹ ^ 4 = 16 / (1 + |x|) ^ 4 := by
    field_simp
  rw [hrewrite]
  by_cases hx : |x| ≤ 1
  · calc
      gaussian x ≤ 1 := aux_gaussian_le_one x
      _ ≤ 16 / (1 + |x|) ^ 4 := by
        apply (le_div_iff₀ hden).2
        have hbase : 1 + |x| ≤ (2 : ℝ) := by linarith
        have hpower : (1 + |x|) ^ 4 ≤ (2 : ℝ) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hbase 4
        norm_num at hpower
        nlinarith
  · have hx' : 1 ≤ |x| := le_of_not_ge hx
    let a : ℝ := Real.pi * x ^ 2
    have ha : 0 ≤ a := by
      dsimp [a]
      positivity
    have hhalf : a / 2 ≤ Real.exp (a / 2) := by
      calc
        a / 2 ≤ 1 + a / 2 := by linarith
        _ ≤ Real.exp (a / 2) := by
          simpa [add_comm] using Real.add_one_le_exp (a / 2)
    have hsquare : (a / 2) ^ 2 ≤ Real.exp (a / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hhalf 2
    have hexpa : (a / 2) ^ 2 ≤ Real.exp a := by
      calc
        (a / 2) ^ 2 ≤ Real.exp (a / 2) ^ 2 := hsquare
        _ = Real.exp a := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
    have hpi2 : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hpi2mul : 2 * x ^ 2 ≤ Real.pi * x ^ 2 :=
      mul_le_mul_of_nonneg_right hpi2 (sq_nonneg _)
    have hrsq : |x| ^ 2 ≤ a / 2 := by
      rw [sq_abs]
      dsimp [a]
      nlinarith
    have hrfour : |x| ^ 4 ≤ (a / 2) ^ 2 := by
      calc
        |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
        _ ≤ (a / 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hrsq 2
    have hrpos : 0 < |x| := lt_of_lt_of_le zero_lt_one hx'
    have hrfourpos : 0 < |x| ^ 4 := pow_pos hrpos _
    have hinv : Real.exp (-a) ≤ (|x| ^ 4)⁻¹ := by
      rw [Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos _) hrfourpos).2 (hrfour.trans hexpa)
    have hscale : (1 + |x|) ^ 4 / 16 ≤ |x| ^ 4 := by
      have hbase : 1 + |x| ≤ 2 * |x| := by linarith
      have hpower : (1 + |x|) ^ 4 ≤ (2 * |x|) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hbase 4
      have htwopow : (2 * |x|) ^ 4 = 16 * |x| ^ 4 := by ring
      rw [htwopow] at hpower
      nlinarith
    have hlast : (|x| ^ 4)⁻¹ ≤ 16 / (1 + |x|) ^ 4 := by
      have hrewrite' : 16 / (1 + |x|) ^ 4 = ((1 + |x|) ^ 4 / 16)⁻¹ := by
        field_simp
      rw [hrewrite']
      exact (inv_le_inv₀ hrfourpos (by positivity)).2 hscale
    calc
      gaussian x = Real.exp (-a) := by simp [a, gaussian, Auto.gaussian]
      _ ≤ (|x| ^ 4)⁻¹ := hinv
      _ ≤ 16 / (1 + |x|) ^ 4 := hlast
end Auto
