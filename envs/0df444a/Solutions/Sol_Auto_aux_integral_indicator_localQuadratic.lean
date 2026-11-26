-- Prove2me | solution 1 for Auto.aux_integral_indicator_localQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:00:07.24391+00:00
-- url     : https://prove2.me/submissions/45bb155c-7c71-4f7b-bb90-a462d7b972db

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
    (∫ x : ℝ, (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun y : ℝ => y ^ 2 + 1 / 4) x) = 1 / 3 := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  have hpow : IntervalIntegrable (fun y : ℝ => y ^ 2) volume
      (-(1 / 2 : ℝ)) (1 / 2) :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 / 4 : ℝ)) volume
      (-(1 / 2 : ℝ)) (1 / 2) :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_add hpow hconst, integral_pow]
  norm_num
end Auto
