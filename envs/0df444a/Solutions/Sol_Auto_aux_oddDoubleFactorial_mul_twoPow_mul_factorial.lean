-- Prove2me | solution 1 for Auto.aux_oddDoubleFactorial_mul_twoPow_mul_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:02.989303+00:00
-- url     : https://prove2.me/submissions/b4e1651f-6b6f-4c71-8083-c4ace5fb4ddc

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
theorem _root_.solution (j : ℕ) :
    Nat.doubleFactorial (2 * j - 1) * (2 ^ j * j.factorial) = (2 * j).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega,
      Nat.doubleFactorial_add_one]
    calc
      (2 * j + 1) * Nat.doubleFactorial (2 * j - 1) *
          (2 ^ (j + 1) * (j + 1).factorial) =
          (2 * j + 2) * (2 * j + 1) *
            (Nat.doubleFactorial (2 * j - 1) * (2 ^ j * j.factorial)) := by
              rw [pow_succ, Nat.factorial_succ]
              ring
      _ = (2 * j + 2) * (2 * j + 1) * (2 * j).factorial := by rw [ih]
      _ = (2 * (j + 1)).factorial := by
        rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega, Nat.factorial_succ]
        rw [show 2 * j + 1 = (2 * j) + 1 by omega, Nat.factorial_succ]
        ring
end Auto
