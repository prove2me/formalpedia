-- Prove2me | solution 1 for Auto.aux_wienerEnvelope_gaussianRescale_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:56:07.049793+00:00
-- url     : https://prove2.me/submissions/9d2e7f51-df41-4422-9c2d-58250d425a7f

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
theorem _root_.solution {t : ℝ} (ht : 0 < t) (x : ℝ) :
    wienerEnvelope (gaussianRescale t) 1 x ≤
      t⁻¹ * Real.exp (Real.pi * t⁻¹ ^ 2) *
        Real.exp (-(Real.pi / 2) * (t⁻¹ * x) ^ 2) := by
  have htin : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  unfold wienerEnvelope
  apply csSup_le
  · exact (Metric.nonempty_closedBall.mpr zero_le_one).image _
  rintro _ ⟨z, hz, rfl⟩
  change ‖t⁻¹ * gaussian (t⁻¹ * (x + z))‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg htin,
    abs_of_pos (aux_gaussian_pos _)]
  have hzabs : |z| ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hz
  have hzsq : z ^ 2 ≤ 1 := by
    rw [← sq_abs z]
    simpa using (sq_le_sq₀ (abs_nonneg z) zero_le_one).mpr hzabs
  have hscaled_z_sq : (t⁻¹ * z) ^ 2 ≤ t⁻¹ ^ 2 := by
    calc
      (t⁻¹ * z) ^ 2 = t⁻¹ ^ 2 * z ^ 2 := by ring
      _ ≤ t⁻¹ ^ 2 * 1 := mul_le_mul_of_nonneg_left hzsq (sq_nonneg _)
      _ = t⁻¹ ^ 2 := by ring
  have hsq_base : (t⁻¹ * x) ^ 2 / 2 - (t⁻¹ * z) ^ 2 ≤
      (t⁻¹ * x + t⁻¹ * z) ^ 2 := by
    nlinarith [sq_nonneg (t⁻¹ * x + 2 * (t⁻¹ * z))]
  have hsq : (t⁻¹ * x) ^ 2 / 2 - t⁻¹ ^ 2 ≤ (t⁻¹ * (x + z)) ^ 2 := by
    calc
      (t⁻¹ * x) ^ 2 / 2 - t⁻¹ ^ 2 ≤
          (t⁻¹ * x) ^ 2 / 2 - (t⁻¹ * z) ^ 2 := sub_le_sub_left hscaled_z_sq _
      _ ≤ (t⁻¹ * x + t⁻¹ * z) ^ 2 := hsq_base
      _ = (t⁻¹ * (x + z)) ^ 2 := by ring
  have hexp : Real.exp (-Real.pi * (t⁻¹ * (x + z)) ^ 2) ≤
      Real.exp (Real.pi * t⁻¹ ^ 2) *
        Real.exp (-(Real.pi / 2) * (t⁻¹ * x) ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, hsq]
  change t⁻¹ * Real.exp (-Real.pi * (t⁻¹ * (x + z)) ^ 2) ≤ _
  calc
    t⁻¹ * Real.exp (-Real.pi * (t⁻¹ * (x + z)) ^ 2) ≤
        t⁻¹ * (Real.exp (Real.pi * t⁻¹ ^ 2) *
          Real.exp (-(Real.pi / 2) * (t⁻¹ * x) ^ 2)) :=
      mul_le_mul_of_nonneg_left hexp htin
    _ = t⁻¹ * Real.exp (Real.pi * t⁻¹ ^ 2) *
        Real.exp (-(Real.pi / 2) * (t⁻¹ * x) ^ 2) := by ring
end Auto
