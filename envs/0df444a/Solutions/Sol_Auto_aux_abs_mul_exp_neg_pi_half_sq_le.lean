-- Prove2me | solution 1 for Auto.aux_abs_mul_exp_neg_pi_half_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:57.404779+00:00
-- url     : https://prove2.me/submissions/973e2c05-cc2c-4a81-b2c4-1a73e2cdc9df

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
    |x| * Real.exp (-(Real.pi / 2) * x ^ 2) ≤
      Real.exp (-(1 / 2) * x ^ 2) := by
  have habs : |x| ≤ Real.exp (x ^ 2) := by
    calc
      |x| ≤ 1 + x ^ 2 := by
        rw [← sq_abs x]
        nlinarith [sq_nonneg (|x| - (1 / 2 : ℝ))]
      _ ≤ Real.exp (x ^ 2) := by
        simpa [add_comm] using Real.add_one_le_exp (x ^ 2)
  calc
    |x| * Real.exp (-(Real.pi / 2) * x ^ 2) ≤
        Real.exp (x ^ 2) * Real.exp (-(Real.pi / 2) * x ^ 2) :=
      mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le
    _ = Real.exp (x ^ 2 + (-(Real.pi / 2) * x ^ 2)) := by rw [← Real.exp_add]
    _ ≤ Real.exp (-(1 / 2) * x ^ 2) := Real.exp_le_exp.mpr (by
      nlinarith [Real.pi_gt_three, sq_nonneg x])
end Auto
