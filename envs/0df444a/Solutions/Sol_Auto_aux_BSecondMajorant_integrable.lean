-- Prove2me | solution 1 for Auto.aux_BSecondMajorant_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:11:05.931213+00:00
-- url     : https://prove2.me/submissions/12eeeea7-491e-42bc-ac5b-c89d7c49cf3e

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
public import Theorems.Thm_Auto_aux_poissonFrequency_integrable

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
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        12 * Real.exp (-(1 / 2) * x ^ 2) +
        8 * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.pi * aux_poissonFrequency x) := by
  have hquad : Integrable ((Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun y : ℝ => y ^ 2 + 1 / 4)) :=
    (((continuous_id.pow 2).add continuous_const).continuousOn.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have hone : Integrable ((Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun _ : ℝ => (1 : ℝ))) :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
      measurableSet_Icc
  have hhalf : Integrable (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  have hpi : Integrable (fun x : ℝ => Real.exp (-(Real.pi / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < Real.pi / 2)
  have hsum :=
    (((hquad.const_mul 144).add (hone.const_mul 4)).add (hhalf.const_mul 12)).add
      ((hpi.const_mul 8).add (aux_poissonFrequency_integrable.const_mul Real.pi))
  refine hsum.congr ?_
  filter_upwards [] with x
  simp only [Pi.add_apply]
  ring
end Auto
