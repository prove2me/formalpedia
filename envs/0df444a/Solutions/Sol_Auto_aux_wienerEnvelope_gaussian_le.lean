-- Prove2me | solution 1 for Auto.aux_wienerEnvelope_gaussian_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:03.438167+00:00
-- url     : https://prove2.me/submissions/3b5ba248-916b-41f2-b334-470e969e8c44

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

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    wienerEnvelope gaussian 1 x ≤
      Real.exp Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) := by
  unfold wienerEnvelope
  apply csSup_le
  · exact (Metric.nonempty_closedBall.mpr zero_le_one).image _
  rintro _ ⟨z, hz, rfl⟩
  change ‖gaussian (x + z)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (aux_gaussian_pos _)]
  change Real.exp (-Real.pi * (x + z) ^ 2) ≤
    Real.exp Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)
  have hzabs : |z| ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hz
  have hzsq : z ^ 2 ≤ 1 := by
    rw [← sq_abs z]
    simpa using (sq_le_sq₀ (abs_nonneg z) zero_le_one).mpr hzabs
  have hsq : x ^ 2 / 2 - 1 ≤ (x + z) ^ 2 := by
    nlinarith [sq_nonneg (x + 2 * z)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_pos, hsq]
end Auto
