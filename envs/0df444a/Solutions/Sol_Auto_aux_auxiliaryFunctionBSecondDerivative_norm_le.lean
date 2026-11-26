-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBSecondDerivative_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:11:05.423123+00:00
-- url     : https://prove2.me/submissions/36b52988-a80c-4254-a823-17aa789864e6

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
public import Theorems.Thm_Auto_aux_exp_neg_abs_sqrt_pi_le_poissonFrequency
public import Theorems.Thm_Auto_aux_BSecondGaussianPart_abs_le_near_zero
public import Theorems.Thm_Auto_aux_BSecondGaussianPart_abs_le_outer

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    ‖auxiliaryFunctionBSecondDerivative x‖ ≤
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        12 * Real.exp (-(1 / 2) * x ^ 2) +
        8 * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.pi * aux_poissonFrequency x := by
  let S : Set ℝ := Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
  let G : ℝ → ℝ := fun y =>
    144 * S.indicator (fun z : ℝ => z ^ 2 + 1 / 4) y +
      4 * S.indicator (fun _ : ℝ => (1 : ℝ)) y +
      12 * Real.exp (-(1 / 2) * y ^ 2) +
      8 * Real.exp (-(Real.pi / 2) * y ^ 2) +
      Real.pi * aux_poissonFrequency y
  change ‖auxiliaryFunctionBSecondDerivative x‖ ≤ G x
  by_cases hx : x ∈ S
  · have hxabs : |x| ≤ 1 / 2 := by
      rw [abs_le]
      simpa [S] using hx
    by_cases hx0 : x = 0
    · subst x
      dsimp [G]
      simp [auxiliaryFunctionBSecondDerivative, S]
      have hpoisson : 0 ≤ aux_poissonFrequency 0 := by
        unfold aux_poissonFrequency
        positivity
      nlinarith [Real.pi_pos]
    · have hquot := aux_BSecondGaussianPart_abs_le_near_zero hx0 hxabs
      have habel_nonneg : 0 ≤ Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
        positivity
      have habel_le_four : Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) ≤ 4 := by
        calc
          Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) ≤ Real.pi * 1 := by
            apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
            exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
          _ ≤ 4 := by simpa using Real.pi_le_four
      have habsquad : |x| ≤ x ^ 2 + 1 / 4 := by
        rw [← sq_abs x]
        nlinarith [sq_nonneg (|x| - (1 / 2 : ℝ))]
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
        _ = |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
                (2 * sqrtOneMinusGaussian x) +
              (-2 * Real.pi * x * gaussian x) ^ 2 /
                (4 * sqrtOneMinusGaussian x ^ 3)| +
              Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
              rw [abs_of_nonneg habel_nonneg]
        _ ≤ 144 * |x| + 4 := add_le_add hquot habel_le_four
        _ ≤ 144 * (x ^ 2 + 1 / 4) + 4 :=
          add_le_add (mul_le_mul_of_nonneg_left habsquad (by norm_num)) le_rfl
        _ ≤ G x := by
          dsimp [G]
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
          have hrest : 0 ≤ 12 * Real.exp (-(1 / 2) * x ^ 2) +
              8 * Real.exp (-(Real.pi / 2) * x ^ 2) +
              Real.pi * aux_poissonFrequency x := by
            unfold aux_poissonFrequency
            positivity
          linarith
  · have hxhalf : 1 / 2 ≤ |x| := by
      apply le_of_not_ge
      intro hsmall
      apply hx
      simpa [S] using (abs_le.mp hsmall)
    have hx0 : x ≠ 0 := by
      intro hzero
      subst x
      apply hx
      simp [S]
    have hquot := aux_BSecondGaussianPart_abs_le_outer hxhalf
    have habel_nonneg : 0 ≤ Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
      positivity
    have habel : Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) ≤
        Real.pi * aux_poissonFrequency x :=
      mul_le_mul_of_nonneg_left (aux_exp_neg_abs_sqrt_pi_le_poissonFrequency x)
        Real.pi_pos.le
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
      _ = |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
              (2 * sqrtOneMinusGaussian x) +
            (-2 * Real.pi * x * gaussian x) ^ 2 /
              (4 * sqrtOneMinusGaussian x ^ 3)| +
            Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
            rw [abs_of_nonneg habel_nonneg]
      _ ≤ 12 * Real.exp (-(1 / 2) * x ^ 2) +
            8 * Real.exp (-(Real.pi / 2) * x ^ 2) +
            Real.pi * aux_poissonFrequency x :=
          add_le_add hquot habel
      _ ≤ G x := by
          dsimp [G]
          rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
          simp only [mul_zero, zero_add]
          exact le_rfl
end Auto
