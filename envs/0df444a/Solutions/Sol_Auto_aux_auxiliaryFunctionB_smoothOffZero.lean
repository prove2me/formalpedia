-- Prove2me | solution 1 for Auto.aux_auxiliaryFunctionB_smoothOffZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:48:15.074689+00:00
-- url     : https://prove2.me/submissions/db1fda36-6339-41e4-befd-2e5b860b455e

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
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) auxiliaryFunctionB ({0}ᶜ : Set ℝ) := by
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx
  have hgauss_lt_one : gaussian x < 1 := by
    have hneg : -Real.pi * x ^ 2 < 0 := by
      nlinarith [Real.pi_pos, sq_pos_of_ne_zero hx0]
    simpa [gaussian, Auto.gaussian] using (Real.exp_lt_exp.mpr hneg)
  have hrad : 1 - gaussian x ≠ 0 := ne_of_gt (sub_pos.mpr hgauss_lt_one)
  have hgaussian : ContDiff ℝ (↑(⊤ : ℕ∞)) gaussian := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => Real.exp (-Real.pi * y ^ 2))
    fun_prop
  have hsqrt : ContDiffAt ℝ (↑(⊤ : ℕ∞)) sqrtOneMinusGaussian x := by
    unfold sqrtOneMinusGaussian
    exact (contDiffAt_const.sub hgaussian.contDiffAt).sqrt hrad
  have hsqrtpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hlinear : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => Real.sqrt Real.pi * y) x := by
    exact (contDiff_const.mul contDiff_id).contDiffAt
  have habsAbs : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (|·| : ℝ → ℝ) (Real.sqrt Real.pi * x) := by
    simpa using
      (contDiffAt_abs (n := (⊤ : ℕ∞)) (mul_ne_zero (ne_of_gt hsqrtpi) hx0))
  have habs : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => |Real.sqrt Real.pi * y|) x :=
    habsAbs.comp x hlinear
  have hexp : ContDiffAt ℝ (↑(⊤ : ℕ∞))
      (fun y : ℝ => Real.exp (-|Real.sqrt Real.pi * y|)) x :=
    Real.contDiff_exp.contDiffAt.comp x habs.neg
  unfold auxiliaryFunctionB
  exact ((contDiffAt_const.sub hsqrt).sub hexp).contDiffWithinAt
end Auto
