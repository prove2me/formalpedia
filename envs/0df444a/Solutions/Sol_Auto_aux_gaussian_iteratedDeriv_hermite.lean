-- Prove2me | solution 1 for Auto.aux_gaussian_iteratedDeriv_hermite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:10.800937+00:00
-- url     : https://prove2.me/submissions/8576d22f-6bb4-4a1c-b664-1a136795fe8c

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
theorem _root_.solution (m : ℕ) (x : ℝ) :
    iteratedDeriv m gaussian x =
      (Real.sqrt (2 * Real.pi)) ^ m *
        ((-1 : ℝ) ^ m * (Polynomial.aeval (Real.sqrt (2 * Real.pi) * x)
          (Polynomial.hermite m)) *
          Real.exp (-((Real.sqrt (2 * Real.pi) * x) ^ 2 / 2))) := by
  let s : ℝ := Real.sqrt (2 * Real.pi)
  let h : ℝ → ℝ := fun y => Real.exp (-(y ^ 2 / 2))
  have hgauss : gaussian = fun z : ℝ => h (s * z) := by
    funext z
    dsimp [h, s, gaussian, Auto.gaussian]
    rw [show (Real.sqrt (2 * Real.pi) * z) ^ 2 = (2 * Real.pi) * z ^ 2 by
      rw [mul_pow, Real.sq_sqrt (by positivity)]]
    congr 1
    ring
  have hh : ContDiff ℝ m h := by
    dsimp [h]
    fun_prop
  rw [hgauss, iteratedDeriv_comp_const_mul hh s]
  change s ^ m * iteratedDeriv m h (s * x) = _
  rw [iteratedDeriv_eq_iterate]
  change s ^ m * deriv^[m] (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) (s * x) = _
  rw [Polynomial.deriv_gaussian_eq_hermite_mul_gaussian]
end Auto
