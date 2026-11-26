-- Prove2me | solution 1 for Auto.aux_two_pi_sqrt_pi_le_twelve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:57.984948+00:00
-- url     : https://prove2.me/submissions/9d36ee99-eb35-4b66-954f-0b0925ed46d3

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
theorem _root_.solution :
    2 * Real.pi * Real.sqrt Real.pi ≤ 12 := by
  have hp : Real.pi ≤ (9 / 5 : ℝ) ^ 2 := by
    nlinarith [Real.pi_lt_d2]
  have hs : Real.sqrt Real.pi ≤ 9 / 5 := by
    calc
      Real.sqrt Real.pi ≤ Real.sqrt ((9 / 5 : ℝ) ^ 2) := Real.sqrt_le_sqrt hp
      _ = 9 / 5 := by rw [Real.sqrt_sq_eq_abs]; norm_num
  have hprod : Real.pi * Real.sqrt Real.pi ≤ (3.15 : ℝ) * (9 / 5 : ℝ) :=
    mul_le_mul (le_of_lt Real.pi_lt_d2) hs (Real.sqrt_nonneg _) (by norm_num)
  nlinarith
end Auto
