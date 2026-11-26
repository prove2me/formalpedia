-- Prove2me | solution 1 for Auto.aux_gaussian_iteratedDeriv_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:24.397411+00:00
-- url     : https://prove2.me/submissions/35f8b4e2-c2c9-48af-b384-77ad0123b99b

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
public import Theorems.Thm_Auto_aux_gaussian_hasDerivAt

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution : ∀ n : ℕ, ∃ p : Polynomial ℝ,
    ∀ x : ℝ, iteratedDeriv n gaussian x = p.eval x * gaussian x := by
  intro n
  induction n with
  | zero =>
      refine ⟨1, ?_⟩
      intro x
      simp
  | succ n ih =>
      rcases ih with ⟨p, hp⟩
      refine ⟨p.derivative + Polynomial.C (-2 * Real.pi) * Polynomial.X * p, ?_⟩
      intro x
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n gaussian = fun x : ℝ => p.eval x * gaussian x := by
        funext z
        exact hp z
      rw [hfun]
      change deriv ((fun z : ℝ => p.eval z) * gaussian) x = _
      rw [((p.hasDerivAt x).mul (aux_gaussian_hasDerivAt x)).deriv]
      simp [Polynomial.eval_add, Polynomial.eval_mul]
      ring
end Auto
