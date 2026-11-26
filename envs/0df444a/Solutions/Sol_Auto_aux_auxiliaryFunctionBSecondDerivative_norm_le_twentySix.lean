-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBSecondDerivative_norm_le_twentySix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:00:16.323562+00:00
-- url     : https://prove2.me/submissions/624473dd-4d2b-4bec-8ee5-62428d4e0c4e

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
public import Theorems.Thm_Auto_aux_exp_three_half_pi_sq_le_four
public import Theorems.Thm_Auto_aux_BSecondGaussianPart_nonneg_le_local

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution {x : ℝ}
    (hx : |x| ≤ 1 / 2) :
    ‖auxiliaryFunctionBSecondDerivative x‖ ≤ 26 := by
  by_cases hx0 : x = 0
  · subst x
    simp [auxiliaryFunctionBSecondDerivative]
  · rcases aux_BSecondGaussianPart_nonneg_le_local hx0 hx with ⟨hpart_nonneg, hpart⟩
    have hscale :
        2 * Real.pi * Real.sqrt Real.pi * |x| *
            Real.exp (3 * (Real.pi * x ^ 2) / 2) ≤
          4 * Real.pi * Real.sqrt Real.pi := by
      calc
        2 * Real.pi * Real.sqrt Real.pi * |x| *
            Real.exp (3 * (Real.pi * x ^ 2) / 2) ≤
            2 * Real.pi * Real.sqrt Real.pi * (1 / 2) * 4 := by
              gcongr
              exact aux_exp_three_half_pi_sq_le_four hx
        _ = 4 * Real.pi * Real.sqrt Real.pi := by ring
    have habel : Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) ≤ Real.pi := by
      calc
        Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) ≤ Real.pi * 1 :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))) Real.pi_pos.le
        _ = Real.pi := by ring
    have hnum : 4 * Real.pi * Real.sqrt Real.pi + Real.pi ≤ 26 := by
      have hpi : Real.pi ≤ (3.1416 : ℝ) := le_of_lt Real.pi_lt_d4
      have hsqrt : Real.sqrt Real.pi ≤ 89 / 50 := by
        calc
          Real.sqrt Real.pi ≤ Real.sqrt ((89 / 50 : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [hpi])
          _ = 89 / 50 := by rw [Real.sqrt_sq_eq_abs]; norm_num
      have hprod : Real.pi * Real.sqrt Real.pi ≤ (3.1416 : ℝ) * (89 / 50) :=
        mul_le_mul hpi hsqrt (Real.sqrt_nonneg _) (by norm_num)
      nlinarith
    rw [Real.norm_eq_abs, auxiliaryFunctionBSecondDerivative, if_neg hx0]
    calc
      |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
            (2 * sqrtOneMinusGaussian x) +
          (-2 * Real.pi * x * gaussian x) ^ 2 /
            (4 * sqrtOneMinusGaussian x ^ 3) -
          Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)| ≤
          |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
              (2 * sqrtOneMinusGaussian x) +
            (-2 * Real.pi * x * gaussian x) ^ 2 /
              (4 * sqrtOneMinusGaussian x ^ 3)| +
            |Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le
                (((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
                    (2 * sqrtOneMinusGaussian x) +
                  (-2 * Real.pi * x * gaussian x) ^ 2 /
                    (4 * sqrtOneMinusGaussian x ^ 3))
                0 (Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)))
      _ = ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
              (2 * sqrtOneMinusGaussian x) +
            (-2 * Real.pi * x * gaussian x) ^ 2 /
              (4 * sqrtOneMinusGaussian x ^ 3) +
            Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
            rw [abs_of_nonneg hpart_nonneg,
              abs_of_nonneg (by positivity : 0 ≤ Real.pi * Real.exp (-|Real.sqrt Real.pi * x|))]
      _ ≤ 4 * Real.pi * Real.sqrt Real.pi + Real.pi :=
        add_le_add (hpart.trans hscale) habel
      _ ≤ 26 := hnum
end Auto
