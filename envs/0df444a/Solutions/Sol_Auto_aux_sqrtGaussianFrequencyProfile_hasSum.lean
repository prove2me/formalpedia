-- Prove2me | solution 1 for Auto.aux_sqrtGaussianFrequencyProfile_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:04:07.113839+00:00
-- url     : https://prove2.me/submissions/e1dfde9d-23e5-49a3-9e60-da4d7980cde7

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
public import Theorems.Thm_Auto_aux_sqrtGaussianCoefficient_hasSum
public import Theorems.Thm_Auto_aux_gaussian_pow_succ_eq

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution {x : ℝ} (hx : x ≠ 0) :
    @HasSum ℝ ℕ Real.instAddCommGroup.toAddCommMonoid _
      (fun n : ℕ => aux_sqrtGaussianCoefficient n *
        gaussian (Real.sqrt (n + 1) * x))
      (1 - sqrtOneMinusGaussian x) (SummationFilter.unconditional ℕ) := by
  have hgauss_lt_one : gaussian x < 1 := by
    have hneg : -Real.pi * x ^ 2 < 0 := by
      nlinarith [Real.pi_pos, sq_pos_of_ne_zero hx]
    simpa [gaussian, Auto.gaussian] using (Real.exp_lt_exp.mpr hneg)
  have hsum := aux_sqrtGaussianCoefficient_hasSum (gaussian x)
    (aux_gaussian_pos x).le hgauss_lt_one
  simpa only [sqrtOneMinusGaussian, aux_gaussian_pow_succ_eq] using hsum
end Auto
