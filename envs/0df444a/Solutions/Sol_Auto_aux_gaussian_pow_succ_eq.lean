-- Prove2me | solution 1 for Auto.aux_gaussian_pow_succ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:24.344675+00:00
-- url     : https://prove2.me/submissions/e9cc9c64-e033-4854-80f4-ba201773a2f3

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
theorem _root_.solution (x : ℝ) (n : ℕ) :
    gaussian x ^ (n + 1) = gaussian (Real.sqrt (n + 1) * x) := by
  change Real.exp (-Real.pi * x ^ 2) ^ (n + 1) =
    Real.exp (-Real.pi * (Real.sqrt (n + 1) * x) ^ 2)
  rw [← Real.exp_nat_mul]
  congr 1
  rw [mul_pow]
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)]
  push_cast
  ring
end Auto
