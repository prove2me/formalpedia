-- Prove2me | solution 1 for Auto.aux_integral_exp_neg_abs_sqrt_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:59.934012+00:00
-- url     : https://prove2.me/submissions/80a87e2b-c8e7-4a7b-91dd-d1c6e93abc3f

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
public import Theorems.Thm_Auto_aux_integral_poissonFrequency

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    (∫ x : ℝ, Real.exp (-|Real.sqrt Real.pi * x|)) = 2 / Real.sqrt Real.pi := by
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  change (∫ x : ℝ, aux_poissonFrequency (Real.sqrt Real.pi * x)) = _
  rw [MeasureTheory.Measure.integral_comp_mul_left,
    aux_integral_poissonFrequency]
  rw [show |(Real.sqrt Real.pi)⁻¹| = (Real.sqrt Real.pi)⁻¹ by
    exact abs_of_pos (inv_pos.mpr hsqrt)]
  simp only [smul_eq_mul]
  ring
end Auto
