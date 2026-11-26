-- Prove2me | solution 1 for Auto.aux_sqrtGaussianCoefficient_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:50.086027+00:00
-- url     : https://prove2.me/submissions/172cf9a6-8450-42a4-a2cc-813ab86e5b5d

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
theorem _root_.solution (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    @HasSum ℝ ℕ Real.instAddCommGroup.toAddCommMonoid _
      (fun n : ℕ => aux_sqrtGaussianCoefficient n * t ^ (n + 1))
      (1 - Real.sqrt (1 - t)) (SummationFilter.unconditional ℕ) := by
  have hmem : edist (-t) (0 : ℝ) < 1 := by
    simp only [edist_dist, dist_zero_right, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg ht0, ENNReal.ofReal_lt_one]
    exact_mod_cast ht1
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (1 / 2 : ℝ))).hasSum
    (Metric.mem_eball.mpr hmem)
  have htail := (hasSum_nat_add_iff' 1).mpr h
  have hneg := htail.neg
  have hfun : (fun n : ℕ =>
      -(binomialSeries ℝ (1 / 2 : ℝ) (n + 1) (fun _ => -t))) =
      (fun n : ℕ => aux_sqrtGaussianCoefficient n * t ^ (n + 1)) := by
    funext n
    simp [binomialSeries, aux_sqrtGaussianCoefficient]
    ring
  rw [hfun] at hneg
  simpa [binomialSeries, Real.sqrt_eq_rpow, sub_eq_add_neg] using hneg
end Auto
