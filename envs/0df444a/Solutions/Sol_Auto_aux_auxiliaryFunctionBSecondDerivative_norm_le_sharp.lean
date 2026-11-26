-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionBSecondDerivative_norm_le_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:22.581492+00:00
-- url     : https://prove2.me/submissions/ba9f0f41-aa2c-405b-928a-0434519e2653

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
public import Theorems.Thm_Auto_aux_auxiliaryFunctionBSecondDerivative_norm_le_twentySix
public import Theorems.Thm_Auto_aux_BSecondGaussianPart_abs_le_outer_sharp

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
      26 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        2 * Real.pi * gaussian x + 12 * Real.pi ^ 2 * x ^ 2 * gaussian x +
          Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
  let S : Set ℝ := Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
  let G : ℝ → ℝ := fun y =>
    26 * S.indicator (fun _ : ℝ => (1 : ℝ)) y +
      2 * Real.pi * gaussian y + 12 * Real.pi ^ 2 * y ^ 2 * gaussian y +
        Real.pi * Real.exp (-|Real.sqrt Real.pi * y|)
  change ‖auxiliaryFunctionBSecondDerivative x‖ ≤ G x
  by_cases hx : x ∈ S
  · have hxabs : |x| ≤ 1 / 2 := by
      rw [abs_le]
      simpa [S] using hx
    calc
      ‖auxiliaryFunctionBSecondDerivative x‖ ≤ 26 :=
        aux_auxiliaryFunctionBSecondDerivative_norm_le_twentySix hxabs
      _ ≤ G x := by
        dsimp [G]
        rw [Set.indicator_of_mem hx]
        have hg : 0 ≤ gaussian x := (aux_gaussian_pos x).le
        have htail : 0 ≤
            2 * Real.pi * gaussian x + 12 * Real.pi ^ 2 * x ^ 2 * gaussian x +
              Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
          have hfirst : 0 ≤ 2 * Real.pi * gaussian x := by positivity
          have hsecond : 0 ≤ 12 * Real.pi ^ 2 * x ^ 2 * gaussian x := by
            positivity
          have hthird : 0 ≤ Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
            positivity
          linarith
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
    have hquot := aux_BSecondGaussianPart_abs_le_outer_sharp hxhalf
    have habel_nonneg : 0 ≤ Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
      positivity
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
      _ ≤ 2 * Real.pi * gaussian x + 12 * Real.pi ^ 2 * x ^ 2 * gaussian x +
              Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) :=
            add_le_add hquot le_rfl
      _ ≤ G x := by
            dsimp [G]
            rw [Set.indicator_of_notMem hx]
            simp only [mul_zero, zero_add]
            exact le_rfl
end Auto
