-- Prove2me | solution 1 for Auto.aux_BSecondSharpMajorant_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:49:23.862269+00:00
-- url     : https://prove2.me/submissions/f03bbf11-77fe-4730-a63f-6ef98e87ebf2

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
public import Theorems.Thm_Auto_aux_gaussian_integrable
public import Theorems.Thm_Auto_aux_exp_neg_abs_sqrt_pi_integrable
public import Theorems.Thm_Auto_aux_sq_mul_gaussian_integrable

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution :
    Integrable (fun x : ℝ =>
      26 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        2 * Real.pi * gaussian x + 12 * Real.pi ^ 2 * x ^ 2 * gaussian x +
          Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)) := by
  have hlocal : Integrable ((Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun _ : ℝ => (1 : ℝ))) :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
      measurableSet_Icc
  have hsum :=
    (((hlocal.const_mul 26).add (aux_gaussian_integrable.const_mul (2 * Real.pi))).add
      (aux_sq_mul_gaussian_integrable.const_mul (12 * Real.pi ^ 2))).add
        (aux_exp_neg_abs_sqrt_pi_integrable.const_mul Real.pi)
  refine hsum.congr ?_
  filter_upwards [] with x
  simp only [Pi.add_apply]
  ring
end Auto
