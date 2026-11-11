-- Prove2me | Definitions.Def_Q226II013
-- name    : Q226II013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:47:43.409381+00:00
-- url     : https://prove2.me/theorems/9b2fcfc0-a5de-4519-8b1c-844de0cf1e9e
-- title:
--   Definitions bundle Q226II013 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 43 declarations of OpenAI's Lean: 9 definitions and 34 theorems. The definitions and types are `OAI.SmoothLocal.Geometry.enumeratedPatchCarrier`, `OAI.SmoothLocal.Geometry.localPatchMetric`, `OAI.SmoothLocal.Pulse.comparisonLowerSourceCoefficient`, `OAI.SmoothLocal.Pulse.comparisonSourceBudget`, `OAI.SmoothLocal.Pulse.curvatureDensityJetError`, `OAI.SmoothLocal.Pulse.qForcingRemainderBudget`, `OAI.SmoothLocal.Pulse.qMomentErrorCoefficient`, `OAI.SmoothLocal.Pulse.testDensityErrorCoefficient`, `OAI.SmoothLocal.Taylor.comparisonTimePolynomial`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Assembly_EnumeratedPatchTensors`, `IsometricImmersion_Assembly_SupportedPerturbations`, `IsometricImmersion_Assembly_SupportedSmoothComplete`, `IsometricImmersion_Caps_PulseReflection`, `IsometricImmersion_Comparison_ActualComparisonEquation`, `IsometricImmersion_Comparison_ActualComparisonSource`, `IsometricImmersion_Comparison_ComparisonEnergyScaling`, `IsometricImmersion_Comparison_ComparisonSourceBounds`, `IsometricImmersion_Comparison_QApproximationMargins`, `IsometricImmersion_Curvature_CurvatureLowerTube`, `IsometricImmersion_Darboux_QMomentAbsorption`, `IsometricImmersion_Estimates_ActualQMomentLower`, `IsometricImmersion_Estimates_ActualQWeightedRemainder`, `IsometricImmersion_Metrics_PatchTensorRestriction`, `IsometricImmersion_Pulses_ActualForcingCoefficient`, `IsometricImmersion_Pulses_ActualForcingMoment`, `IsometricImmersion_Pulses_ActualTwoSidedPulseSeparation`, `IsometricImmersion_Pulses_ForcingCoefficientSign`, `IsometricImmersion_Pulses_PulseDensitySlab`, `IsometricImmersion_Pulses_PulseFirstJetControl`, `IsometricImmersion_Pulses_PulseSecondXi`, `IsometricImmersion_Taylor_FiniteTaylorComparison`, `IsometricImmersion_Taylor_TaylorInitialVelocity`, `IsometricImmersion_Taylor_TaylorResidual`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II007`, `Q226II008`, `Q226II009` and `Q226II010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q226II015` and `Q226II016`.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 334; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.Count
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Encodable.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Order.Interval.Set.Pi
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Closure
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_IsometricImmersion
import Definitions.Def_Q226II007
import Definitions.Def_Q226II008
import Definitions.Def_Q226II009
import Definitions.Def_Q226II010

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_SupportedPerturbations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter TopologicalSpace

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Model

theorem symmetricSupportedSubmodule_isClosed :
    IsClosed (symmetricSupportedSubmodule : Set SupportedTensor) := by
  change IsClosed {η : SupportedTensor | ∀ p i j, η p i j = η p j i}
  simp only [ofPred_forall]
  exact isClosed_iInter (fun p => isClosed_iInter (fun i => isClosed_iInter (fun j =>
    isClosed_eq (supportedTensor_eval_continuous p i j) (supportedTensor_eval_continuous p j i))))

theorem perturbationTensor_tsupport_subset (η : SymmetricPerturbation) :
    tsupport (perturbationTensor η) ⊆ patchBox := η.val.tsupport_subset

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_EnumeratedPatchTensors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

def enumeratedPatchCarrier (j : ℕ) : Set Coord :=
  match patchTensorAddress j with
  | none => ∅
  | some a => patchAddressCarrier a

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_SupportedSmoothComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter TopologicalSpace
open scoped BoundedContinuousFunction

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem symmetricPerturbation_completelyMetrizable :
    IsCompletelyMetrizableSpace SymmetricPerturbation := by
  let : IsCompletelyMetrizableSpace SupportedTensor := supportedSmooth_completelyMetrizable patchCompact
  exact symmetricSupportedSubmodule_isClosed.isClosedEmbedding_subtypeVal.IsCompletelyMetrizableSpace

theorem symmetricPerturbation_baire : BaireSpace SymmetricPerturbation := by
  let : IsCompletelyMetrizableSpace SymmetricPerturbation := symmetricPerturbation_completelyMetrizable
  infer_instance

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_PulseReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow.Reflection

theorem reflected_pulse_approximation_jet_norm
    (gTau gStar : MetricField) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    (i j : Fin 2) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (fun q => reflectedMetric gTau q i j-
      testMetric (reflectedMetric gStar) (-q0) a N delta tau q i j) p‖ =
    ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
      testMetric gStar q0 a N delta tau q i j) (reflectPoint p)‖ := by
  have hfun : (fun q => reflectedMetric gTau q i j-
      testMetric (reflectedMetric gStar) (-q0) a N delta tau q i j) =
      (fun q => reflectedMetric (gTau-testMetric gStar q0 a N delta tau) q i j) := by
    funext q
    simp only [← reflectedMetric_testMetric,reflectedMetric_sub,Pi.sub_apply,Matrix.sub_apply]
  rw [hfun]
  exact reflectedMetric_entry_jet_norm _ p i j k

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ActualForcingCoefficient
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem forcingCoefficient_contDiffOn {g : MetricField} {z : Coord → ℝ}
    {U S : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hSU : S ⊆ U)
    (hxx : ∀ p ∈ S, covHessian g z p 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (forcingCoefficient g z) S := by
  apply (contDiffOn_const.sub ((covectorNormSq_contDiffOn hg hU hz).mono hSU)).div
    (contDiffOn_const.mul ((covHessian_contDiffOn hg hU hz 0 0).mono hSU))
  intro p hp
  exact mul_ne_zero (by norm_num) (hxx p hp)

theorem forcingCoefficient_one_sign {g : MetricField} {z : Coord → ℝ}
    {U S : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hSU : S ⊆ U) (hS : IsPreconnected S)
    (hE : ∀ p ∈ S, 0 < heightEnergy g z p)
    (hxx : ∀ p ∈ S, covHessian g z p 0 0 ≠ 0) :
    ∀ p ∈ S, ∀ q ∈ S, 0 < forcingCoefficient g z p * forcingCoefficient g z q := by
  have hcont := (forcingCoefficient_contDiffOn hg hz hU hSU hxx).continuousOn
  have hne (p : Coord) (hp : p ∈ S) : forcingCoefficient g z p ≠ 0 := by
    rw [forcingCoefficient_eq_energy hg z (hSU hp)]
    exact div_ne_zero (hE p hp).ne'
      (mul_ne_zero (mul_ne_zero (by norm_num) (metricDet_ne_zero hg (hSU hp))) (hxx p hp))
  intro p hp q hq
  rcases lt_or_gt_of_ne (hne p hp) with hpneg | hppos
  · have hqneg : forcingCoefficient g z q < 0 := by
      by_contra hn
      obtain ⟨b, hb, heq⟩ := hS.intermediate_value₂ hp hq hcont continuousOn_const
        hpneg.le (le_of_not_gt hn)
      exact hne b hb heq
    exact mul_pos_of_neg_of_neg hpneg hqneg
  · have hqpos : 0 < forcingCoefficient g z q := by
      by_contra hn
      obtain ⟨b, hb, heq⟩ := hS.intermediate_value₂ hq hp hcont continuousOn_const
        (le_of_not_gt hn) hppos.le
      exact hne b hb heq
    exact mul_pos hppos hqpos

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_CurvatureLowerTube
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem exists_uniform_thetaPulseLowerDifference_bound (B : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (f : Coord → ℝ) (p : Coord),
      ‖actualCurvatureFirstInput g p‖ ≤ B → d ≤ (g p).det →
      ‖thetaCurvatureFirstIncrement f p‖ ≤ 1 → |g p 0 0| * |f p| ≤ d/2 →
      |thetaPulseLowerDifference g f p| ≤ C*‖thetaCurvatureFirstIncrement f p‖ := by
  obtain ⟨C,hC,hbound⟩ := curvatureFirstTube_fderiv_bound (B+1) (half_pos hd)
  refine ⟨C,hC,?_⟩
  intro g f p hg hdet hincr hsmall
  let a := actualCurvatureFirstInput g p
  let b := a+thetaCurvatureFirstIncrement f p
  have ha : ‖a‖ ≤ B+1 := hg.trans (by linarith)
  have hb : ‖b‖ ≤ B+1 := (norm_add_le _ _).trans (add_le_add hg hincr)
  have hda : d/2 ≤ (Matrix.of a.1).det := (by linarith : d/2 ≤ d).trans hdet
  have hdetEq : (Matrix.of b.1).det = (g p).det+g p 0 0*f p := by
    simp only [b,a,actualCurvatureFirstInput,thetaCurvatureFirstIncrement,
      Matrix.det_fin_two,Prod.fst_add,Pi.add_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.of_apply]
    ring
  have hdb : d/2 ≤ (Matrix.of b.1).det := by
    rw [hdetEq]
    have hprod : -(d/2) ≤ g p 0 0*f p := by
      have h := neg_abs_le (g p 0 0*f p)
      rw [abs_mul] at h
      linarith
    linarith
  have htube := theta_first_segment_subset_tube a f p ha hb hda hdb
  have hdiff : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ curvatureFirstFunction x := by
    intro x hx
    exact (curvatureFirstFunction_contDiffOn.contDiffAt
      (curvatureFirstDomain_isOpen.mem_nhds
        (curvatureFirstTube_subset_domain (B+1) (half_pos hd) (htube hx)))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h := (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le hdiff
    (fun x hx => hbound x (htube hx)) (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  simpa only [b,a,thetaPulseLowerDifference_eq_firstFunction,Real.norm_eq_abs,
    add_sub_cancel_left] using h

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseFirstJetControl
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem scalarPulseFirstJetBudget_tendsto_zero {a : ℝ} (ha : 0 < a) (N : ℕ)
    (hN : 1 < N) (delta : ℝ) :
    Tendsto (scalarPulseFirstJetBudget a ha N delta) atTop (𝓝 0) := by
  have hn : N-1 ≠ 0 := by omega
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).pow (N-1)
  have h : Tendsto (fun t : ℝ => scalarPulseFirstJetBound a ha delta*(t⁻¹)^(N-1)) atTop (𝓝 0) := by
    simpa only [zero_pow hn,mul_zero] using hi.const_mul (scalarPulseFirstJetBound a ha delta)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hN' : N = 1+(N-1) := by omega
  have hr : t/t^N = (t⁻¹)^(N-1) := by
    conv_lhs => rw [hN',pow_add,pow_one]
    rw [inv_pow]
    field_simp [ht.ne']
  simp only [scalarPulseFirstJetBudget,mul_div_assoc,hr]

theorem exists_uniform_actual_pulse_lower_bound (B : ℝ) {d : ℝ} (hd : 0 < d)
    {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, ∃ T : ℝ, 1 ≤ T ∧
      ∀ tau : ℝ, T ≤ tau → ∀ (g : MetricField) (p : Coord),
        ‖actualCurvatureFirstInput g p‖ ≤ B → d ≤ (g p).det →
        |thetaPulseLowerDifference g (pulseScalar a N delta tau) p| ≤
          C*scalarPulseFirstJetBudget a ha N delta tau := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_thetaPulseLowerDifference_bound B hd
  refine ⟨C,hC,?_⟩
  intro delta
  let beta := max B 0+1
  have hbeta : 0 < beta := by dsimp only [beta] <;> linarith [le_max_right B 0]
  let e := min 1 (d/(2*beta))
  have he : 0 < e := lt_min zero_lt_one (div_pos hd (mul_pos (by norm_num) hbeta))
  have hev : ∀ᶠ tau : ℝ in atTop, scalarPulseFirstJetBudget a ha N delta tau < e :=
    (scalarPulseFirstJetBudget_tendsto_zero ha N hN delta).eventually (eventually_lt_nhds he)
  obtain ⟨T,hT⟩ := eventually_atTop.mp hev
  refine ⟨max T 1,le_max_right _ _,?_⟩
  intro tau ht g p hg hdet
  have ht1 : 1 ≤ tau := (le_max_right _ _).trans ht
  have htT : T ≤ tau := (le_max_left _ _).trans ht
  have hsmall1 : scalarPulseFirstJetBudget a ha N delta tau ≤ 1 :=
    (hT tau htT).le.trans (min_le_left _ _)
  have hsmallD : scalarPulseFirstJetBudget a ha N delta tau ≤ d/(2*beta) :=
    (hT tau htT).le.trans (min_le_right _ _)
  have hg00 : |g p 0 0| ≤ beta := by
    have h0 : |g p 0 0| ≤ ‖actualCurvatureFirstInput g p‖ := by
      simpa only [Real.norm_eq_abs] using
        ((norm_le_pi_norm (g p 0) 0).trans (norm_le_pi_norm (g p) 0)).trans
          (norm_fst_le (actualCurvatureFirstInput g p))
    exact (h0.trans hg).trans (by dsimp only [beta] <;> linarith [le_max_left B 0])
  have hproduct : |g p 0 0| * |pulseScalar a N delta tau p| ≤ d/2 := by
    calc
      _ ≤ beta*scalarPulseFirstJetBudget a ha N delta tau :=
        mul_le_mul hg00 (pulseScalar_first_jet_bounds ha N delta ht1 p).1
          (abs_nonneg _) hbeta.le
      _ ≤ beta*(d/(2*beta)) := mul_le_mul_of_nonneg_left hsmallD hbeta.le
      _ = d/2 := by field_simp [hbeta.ne']
  have hinc := thetaPulse_first_increment_bound ha N delta ht1 p
  exact (hbound g (pulseScalar a N delta tau) p hg hdet (hinc.trans hsmall1) hproduct).trans
    (mul_le_mul_of_nonneg_left hinc hC)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseSecondXi
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem pulseScalar_xixi (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    coordPartial 0 (coordPartial 0 (pulseScalar a N delta tau)) p =
      (1/tau^N)*temporalCutoff (tau*p 1/delta)*
        (deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0)-
          2*tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)-
            tau^2*axisBump a (p 0)*Real.cos (tau*p 0)) := by
  have hf : ContDiff ℝ ∞ (coordPartial 0 (pulseScalar a N delta tau)) :=
    contDiffOn_univ.mp (partial_contDiffOn
      (pulseScalar_contDiff a N delta tau).contDiffOn isOpen_univ 0)
  rw [coordPartial_xi_eq_line_deriv (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  have he : (fun x => coordPartial 0 (pulseScalar a N delta tau) (coordinatePoint x (p 1))) =
      (fun x => (1/tau^N)*temporalCutoff (tau*p 1/delta)*
        (deriv (axisBump a) x*Real.cos (tau*x)-tau*axisBump a x*Real.sin (tau*x))) := by
    funext x
    rw [pulseScalar_xi]
    simp [coordinatePoint]
  rw [he]
  exact (pulseXiLine_hasDerivAt a N delta tau (p 0) (p 1)).deriv

theorem pulse_principal_exact (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    -(1/2 : ℝ)*coordPartial 0 (coordPartial 0 (pulseScalar a N delta tau)) p =
      pulsePrincipalLeading a N delta tau p + pulsePrincipalRemainder a N delta tau p := by
  rw [pulseScalar_xixi]
  unfold pulsePrincipalLeading pulsePrincipalRemainder
  ring

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseDensitySlab
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def curvatureDensityJetError (g h : MetricField) (p : Coord) : ℝ :=
  (coordPartial 0 (coordPartial 1 (fun q => g q 0 1)) p-
    coordPartial 0 (coordPartial 1 (fun q => h q 0 1)) p) -
  ((coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p-
      coordPartial 0 (coordPartial 0 (fun q => h q 1 1)) p) +
    (coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p-
      coordPartial 1 (coordPartial 1 (fun q => h q 0 0)) p))/2 +
  curvatureLowerTerm g p-curvatureLowerTerm h p

theorem curvatureDensityJetError_le (g h : MetricField) (p : Coord) {e : ℝ}
    (hxy : |coordPartial 0 (coordPartial 1 (fun q => g q 0 1)) p-
      coordPartial 0 (coordPartial 1 (fun q => h q 0 1)) p| ≤ e)
    (hxx : |coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p-
      coordPartial 0 (coordPartial 0 (fun q => h q 1 1)) p| ≤ e)
    (hyy : |coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p-
      coordPartial 1 (coordPartial 1 (fun q => h q 0 0)) p| ≤ e) :
    |curvatureDensityJetError g h p| ≤ 2*e+|curvatureLowerTerm g p-curvatureLowerTerm h p| := by
  let x := coordPartial 0 (coordPartial 1 (fun q => g q 0 1)) p-
    coordPartial 0 (coordPartial 1 (fun q => h q 0 1)) p
  let y := coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p-
    coordPartial 0 (coordPartial 0 (fun q => h q 1 1)) p
  let z := coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p-
    coordPartial 1 (coordPartial 1 (fun q => h q 0 0)) p
  have hmain : |x-(y+z)/2| ≤ 2*e := by
    calc
      _ ≤ |x|+|(y+z)/2| := abs_sub _ _
      _ = |x|+|y+z|/2 := by rw [abs_div]; norm_num
      _ ≤ e+(e+e)/2 := add_le_add hxy
        (div_le_div_of_nonneg_right ((abs_add_le y z).trans (add_le_add hxx hyy)) (by norm_num))
      _ = 2*e := by ring
  have heq : curvatureDensityJetError g h p =
      (x-(y+z)/2)+(curvatureLowerTerm g p-curvatureLowerTerm h p) := by
    dsimp only [curvatureDensityJetError,x,y,z]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hmain le_rfl)

def testDensityErrorCoefficient (C a : ℝ) (ha : 0 < a) (delta : ℝ) : ℝ :=
  pulsePrincipalRemainderBound a ha+C*scalarPulseFirstJetBound a ha delta

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ForcingCoefficientSign
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem actual_forcingCoefficient_signed_floor
    {g : MetricField} {z : Coord → ℝ} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hSU : S ⊆ U) (hS : IsPreconnected S)
    {p0 : Coord} (hp0 : p0 ∈ S) {e c D C : ℝ} (he : 0 < e) (hc : 0 < c)
    (hE : ∀ p ∈ S, e ≤ heightEnergy g z p)
    (hdet : ∀ p ∈ S, (g p).det ≤ D)
    (hxx : ∀ p ∈ S, c ≤ |covHessian g z p 0 0|)
    (hxxup : ∀ p ∈ S, |covHessian g z p 0 0| ≤ C) :
    ∃ sigma : ℝ, |sigma| = 1 ∧ ∀ p ∈ S,
      sigma*forcingCoefficient g z p = |forcingCoefficient g z p| ∧
      forcingFloor e D C ≤ sigma*forcingCoefficient g z p := by
  have hxxne : ∀ p ∈ S, covHessian g z p 0 0 ≠ 0 := by
    intro p hp hz0
    have hh := hxx p hp
    rw [hz0,abs_zero] at hh
    linarith
  have hsign := forcingCoefficient_one_sign hg hz hU hSU hS
    (fun p hp => he.trans_le (hE p hp)) hxxne
  have hfloor (p : Coord) (hp : p ∈ S) :=
    forcingCoefficient_floor_of_reference_margins hg (hSU hp) he hc
      (hE p hp) (hdet p hp) (hxx p hp) (hxxup p hp)
  have hanchor : forcingCoefficient g z p0 ≠ 0 :=
    abs_pos.mp ((forcingFloor_pos he D C).trans_le (hfloor p0 hp0))
  rcases lt_or_gt_of_ne hanchor with hneg | hpos
  · refine ⟨-1,by norm_num,?_⟩
    intro p hp
    have hpneg : forcingCoefficient g z p < 0 := by
      by_contra hn
      have hn0 : 0 ≤ forcingCoefficient g z p := le_of_not_gt hn
      have hnonpos := mul_nonpos_of_nonpos_of_nonneg hneg.le hn0
      linarith [hsign p0 hp0 p hp]
    constructor
    · rw [abs_of_neg hpneg]
      ring
    · simpa only [neg_one_mul,abs_of_neg hpneg] using hfloor p hp
  · refine ⟨1,by norm_num,?_⟩
    intro p hp
    have hppos : 0 < forcingCoefficient g z p := by
      by_contra hn
      have hn0 : forcingCoefficient g z p ≤ 0 := le_of_not_gt hn
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos hpos.le hn0
      linarith [hsign p0 hp0 p hp]
    constructor
    · rw [one_mul,abs_of_pos hppos]
    · simpa only [one_mul,abs_of_pos hppos] using hfloor p hp

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ActualForcingMoment
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem exists_actual_leading_forcing_moment_lower {a e c : ℝ}
    (ha : 0 < a) (he : 0 < e) (hc : 0 < c) (D C : ℝ) (N : ℕ) :
    ∃ c3 : ℝ, 0 < c3 ∧ ∀ᶠ tau : ℝ in atTop,
      ∀ delta : ℝ, 0 < delta → ∀ (g : MetricField) (z : Coord → ℝ) (U : Set Coord),
        SmoothPositiveOn g U → ContDiffOn ℝ ∞ z U → IsOpen U →
        pulseStrip a delta tau ⊆ U →
        (∀ p ∈ pulseStrip a delta tau, e ≤ heightEnergy g z p) →
        (∀ p ∈ pulseStrip a delta tau, (g p).det ≤ D) →
        (∀ p ∈ pulseStrip a delta tau, c ≤ |covHessian g z p 0 0|) →
        (∀ p ∈ pulseStrip a delta tau, |covHessian g z p 0 0| ≤ C) →
        c3*delta*tau/tau^N ≤
          |pulseWeightedMoment a delta tau
            (fun p => 2*forcingCoefficient g z p*pulsePrincipalLeading a N delta tau p)| := by
  obtain ⟨cs,hcs,hspatial⟩ := spatialCutoff_cos_sq_moment_eventually_lower ha
  let c3 := forcingFloor e D C*(∫ theta : ℝ, temporalCutoff theta)*cs
  have hc3 : 0 < c3 := mul_pos
    (mul_pos (forcingFloor_pos he D C) temporalCutoff_integral_pos) hcs
  refine ⟨c3,hc3,?_⟩
  filter_upwards [hspatial,eventually_gt_atTop (0 : ℝ)] with tau hspatialTau ht
  intro delta hd g z U hg hz hU hSU hE hdet hxx hxxup
  obtain ⟨sigma,hsigma,hsigned⟩ := actual_forcingCoefficient_signed_floor hg hz hU hSU
    (closedRectangle_isPreconnected (-a) a (-(delta/tau)) (delta/tau))
    (pulseStrip_zero_mem ha.le hd.le ht) he hc hE hdet hxx hxxup
  have hxxne : ∀ p ∈ pulseStrip a delta tau, covHessian g z p 0 0 ≠ 0 := by
    intro p hp hz0
    have h := hxx p hp
    rw [hz0,abs_zero] at h
    linarith
  have hcont := (forcingCoefficient_contDiffOn hg hz hU hSU hxxne).continuousOn
  have hmoment := signed_coefficient_weighted_integral_lower hcont hsigma
    (fun p hp => (hsigned p hp).2)
  rw [pulseMomentWeight_integral ha hd ht] at hmoment
  have hscale : 0 ≤ tau^2/tau^N := div_nonneg (sq_nonneg tau) (pow_nonneg ht.le N)
  rw [actual_leading_weighted_moment_eq g z a delta N ht,abs_mul,abs_of_nonneg hscale]
  calc
    c3*delta*tau/tau^N = (tau^2/tau^N)*
      (forcingFloor e D C*((delta/tau)*(∫ theta : ℝ, temporalCutoff theta)*cs)) := by
        dsimp only [c3]
        field_simp [ht.ne']
    _ ≤ (tau^2/tau^N)*(forcingFloor e D C*((delta/tau)*
        (∫ theta : ℝ, temporalCutoff theta)*
          (∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2))) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      apply mul_le_mul_of_nonneg_left _ (forcingFloor_pos he D C).le
      exact mul_le_mul_of_nonneg_left hspatialTau
        (mul_nonneg (div_nonneg hd.le ht.le) temporalCutoff_integral_pos.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left hmoment hscale

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualQWeightedRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def qForcingRemainderBudget (A Cfirst Ctest Ccompare a : ℝ) (ha : 0 < a)
    (N : ℕ) (delta tau epsilon epsilonQ : ℝ) : ℝ :=
  2*A*(testDensityErrorCoefficient Ctest a ha delta*tau/tau^N+Ccompare*epsilon)+Cfirst*epsilonQ

theorem qForcingRemainderBudget_nonneg {A Cfirst Ctest Ccompare a : ℝ} (ha : 0 < a)
    (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst) (hCt : 0 ≤ Ctest) (hCc : 0 ≤ Ccompare)
    (N : ℕ) (delta : ℝ) {tau epsilon epsilonQ : ℝ}
    (ht : 0 ≤ tau) (he : 0 ≤ epsilon) (heQ : 0 ≤ epsilonQ) :
    0 ≤ qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ := by
  have hCd : 0 ≤ testDensityErrorCoefficient Ctest a ha delta :=
    add_nonneg (pulsePrincipalRemainderBound_nonneg a ha)
      (mul_nonneg hCt (scalarPulseFirstJetBound_nonneg ha delta))
  unfold qForcingRemainderBudget
  positivity

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualQMomentLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem actualShearedQLeading_contDiffOn {gStar : MetricField} {z : Coord → ℝ}
    {U S : Set Coord} (hg : SmoothPositiveOn gStar U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    (hSU : ∀ p ∈ S, inverseShearCoordinates q0 p ∈ U)
    (hxx : ∀ p ∈ S, covHessian (metricInShearCoordinates gStar q0)
      (heightInShearCoordinates z q0) p 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (actualShearedQLeading gStar z q0 a N delta tau) S := by
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hgV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hg 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hzV : ContDiffOn ℝ ∞ (heightInShearCoordinates z q0) V :=
    heightInShearCoordinates_contDiffOn hz q0
  have hSV : S ⊆ V := fun p hp => hSU p hp
  exact (contDiffOn_const.mul (forcingCoefficient_contDiffOn hgV hzV hV hSV hxx)).mul
    (pulsePrincipalLeading_contDiff a N delta tau).contDiffOn

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QMomentAbsorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def qMomentErrorCoefficient (A Cfirst Ctest Ccompare a : ℝ) (ha : 0 < a) (delta : ℝ) : ℝ :=
  2*A*(testDensityErrorCoefficient Ctest a ha delta+Ccompare)+
    Cfirst*(8+scalarPulseFirstJetBound a ha delta)

theorem qMomentErrorCoefficient_nonneg {A Cfirst Ctest Ccompare a : ℝ} (ha : 0 < a)
    (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst) (hCt : 0 ≤ Ctest) (hCc : 0 ≤ Ccompare) (delta : ℝ) :
    0 ≤ qMomentErrorCoefficient A Cfirst Ctest Ccompare a ha delta := by
  have hCd : 0 ≤ testDensityErrorCoefficient Ctest a ha delta :=
    add_nonneg (pulsePrincipalRemainderBound_nonneg a ha)
      (mul_nonneg hCt (scalarPulseFirstJetBound_nonneg ha delta))
  unfold qMomentErrorCoefficient
  exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) (add_nonneg hCd hCc))
    (mul_nonneg hCf (add_nonneg (by norm_num) (scalarPulseFirstJetBound_nonneg ha delta)))

theorem qForcingRemainderBudget_le_first_scale
    {A Cfirst Ctest Ccompare a delta tau epsilon epsilonQ : ℝ} {N : ℕ} (ha : 0 < a)
    (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst) (hCc : 0 ≤ Ccompare)
    (he : epsilon ≤ tau/tau^N) (heQ : epsilonQ ≤ qPulseFirstJetBudget a ha N delta tau) :
    qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ ≤
      qMomentErrorCoefficient A Cfirst Ctest Ccompare a ha delta*tau/tau^N := by
  unfold qForcingRemainderBudget
  calc
    _ ≤ 2*A*(testDensityErrorCoefficient Ctest a ha delta*tau/tau^N+Ccompare*(tau/tau^N))+
        Cfirst*qPulseFirstJetBudget a ha N delta tau :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left he hCc)) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA))
        (mul_le_mul_of_nonneg_left heQ hCf)
    _ = _ := by unfold qMomentErrorCoefficient qPulseFirstJetBudget; ring

theorem qMoment_budget_absorption_threshold
    {A Cfirst Ctest Ccompare a c3 : ℝ} (ha : 0 < a) (hc3 : 0 < c3)
    (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst) (hCt : 0 ≤ Ctest) (hCc : 0 ≤ Ccompare)
    (N : ℕ) (delta : ℝ) (hdelta : 0 ≤ delta) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ tau : ℝ, T ≤ tau → ∀ epsilon epsilonQ : ℝ,
      epsilon ≤ tau/tau^N → epsilonQ ≤ qPulseFirstJetBudget a ha N delta tau →
      qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ*
        (2*delta/tau)*(∫ x : ℝ, axisBump a x) ≤ (c3/2)*delta*tau/tau^N := by
  let K := qMomentErrorCoefficient A Cfirst Ctest Ccompare a ha delta
  let I := ∫ x : ℝ, axisBump a x
  have hK : 0 ≤ K := qMomentErrorCoefficient_nonneg ha hA hCf hCt hCc delta
  have hI : 0 ≤ I := (axisBump_integral_pos ha).le
  refine ⟨max 1 (4*K*I/c3),le_max_left _ _,?_⟩
  intro tau ht epsilon epsilonQ he heQ
  have ht1 : 1 ≤ tau := (le_max_left _ _).trans ht
  have htpos : 0 < tau := zero_lt_one.trans_le ht1
  have hthreshold : 4*K*I/c3 ≤ tau := (le_max_right _ _).trans ht
  have hcoeff : 2*K*I ≤ (c3/2)*tau := by
    have hh := (div_le_iff₀ hc3).mp hthreshold
    nlinarith
  have hB := qForcingRemainderBudget_le_first_scale (Ctest := Ctest) ha hA hCf hCc he heQ
  have hwidth : 0 ≤ 2*delta/tau := div_nonneg (mul_nonneg (by norm_num) hdelta) htpos.le
  have hscale : 0 ≤ delta/tau^N := div_nonneg hdelta (pow_nonneg htpos.le N)
  calc
    _ ≤ (K*tau/tau^N)*(2*delta/tau)*I :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hwidth) hI
    _ = (2*K*I)*(delta/tau^N) := by field_simp [htpos.ne']
    _ ≤ ((c3/2)*tau)*(delta/tau^N) := mul_le_mul_of_nonneg_right hcoeff hscale
    _ = _ := by ring

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem comparisonDomain_denominator {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} {p : Coord}
    (hp : p ∈ comparisonDomain g U P I) :
    p ∈ U ∧ covHessian g P p 0 0 ≠ 0 := by
  exact ⟨by simpa only [statePoint_qSolutionJet] using hp.2.1,
    by simpa only [stateQDenominator_qSolutionJet] using hp.2.2⟩

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualComparisonSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Taylor

theorem actualComparisonSource_moment {gStar gTau : MetricField} {z P : Coord → ℝ}
    {q0 a delta tau : ℝ}
    (hQ : ContinuousOn (actualShearedQForcing gStar gTau z q0) (pulseStrip a delta tau))
    (hP : ContinuousOn (qResidual (metricInShearCoordinates gStar q0) P)
      (pulseStrip a delta tau)) :
    pulseWeightedMoment a delta tau (actualComparisonSource gStar gTau z q0 P) =
      pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0) -
        pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P) :=
  pulseWeightedMoment_sub hQ hP

theorem actualComparisonSource_moment_triangle {gStar gTau : MetricField} {z P : Coord → ℝ}
    {q0 a delta tau : ℝ}
    (hQ : ContinuousOn (actualShearedQForcing gStar gTau z q0) (pulseStrip a delta tau))
    (hP : ContinuousOn (qResidual (metricInShearCoordinates gStar q0) P)
      (pulseStrip a delta tau)) :
    |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)| -
      |pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)| ≤
        |pulseWeightedMoment a delta tau (actualComparisonSource gStar gTau z q0 P)| := by
  rw [actualComparisonSource_moment hQ hP]
  have ht : |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)| ≤
      |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0) -
        pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)| +
      |pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)| := by
    calc
      _ = |(pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0) -
        pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)) +
          pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)| := by
            congr 1
            ring
      _ ≤ _ := abs_add_le _ _
  linarith

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualComparisonEquation
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Taylor
open SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem comparison_initial_partials_zero
    {U : Set Coord} {P z : Coord → ℝ} (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U)
    {left right a : ℝ} (hcut : ∀ x ∈ Ioo left right, boxPoint x a ∈ U)
    (hvalue : ∀ x ∈ Ioo left right, P (boxPoint x a) = z (boxPoint x a))
    (hvelocity : ∀ x ∈ Ioo left right, coordPartial 1 P (boxPoint x a) = coordPartial 1 z (boxPoint x a))
    {x : ℝ} (hx : x ∈ Ioo left right) :
    coordPartial 0 (comparisonDifference P z) (boxPoint x a) = 0 ∧
    coordPartial 1 (comparisonDifference P z) (boxPoint x a) = 0 := by
  have hj := qSolutionJet_eq_of_cauchy_data hz hP hU hcut hvalue hvelocity hx
  have hxEq : coordPartial 0 P (boxPoint x a) = coordPartial 0 z (boxPoint x a) :=
    congrArg (fun w : DarbouxState => w 2) hj
  have h0 := CoordinateBound.iterated_sub hz hP hU [0] (hcut x hx)
  have h1 := CoordinateBound.iterated_sub hz hP hU [1] (hcut x hx)
  change coordPartial 0 (comparisonDifference P z) (boxPoint x a) =
    coordPartial 0 z (boxPoint x a)-coordPartial 0 P (boxPoint x a) at h0
  change coordPartial 1 (comparisonDifference P z) (boxPoint x a) =
    coordPartial 1 z (boxPoint x a)-coordPartial 1 P (boxPoint x a) at h1
  exact ⟨by rw [h0,hxEq,sub_self],by rw [h1,hvelocity x hx,sub_self]⟩

theorem comparison_initial_energy_zero
    {U : Set Coord} {P z S : Coord → ℝ} (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U)
    {left right xl xr a : ℝ} (hlr : xl ≤ xr)
    (hcut : ∀ x ∈ Ioo left right, boxPoint x a ∈ U)
    (hvalue : ∀ x ∈ Ioo left right, P (boxPoint x a) = z (boxPoint x a))
    (hvelocity : ∀ x ∈ Ioo left right, coordPartial 1 P (boxPoint x a) = coordPartial 1 z (boxPoint x a))
    (hxl : left < xl) (hxr : xr < right) :
    (∫ x in xl..xr, energyDensity S (comparisonDifference P z) (coordinatePoint x a)) = 0 := by
  have hpoint (x : ℝ) (hx : x ∈ uIcc xl xr) :
      energyDensity S (comparisonDifference P z) (coordinatePoint x a) = 0 := by
    have hx' : x ∈ Icc xl xr := by simpa only [uIcc_of_le hlr] using hx
    have hi : x ∈ Ioo left right := ⟨hxl.trans_le hx'.1,hx'.2.trans_lt hxr⟩
    obtain ⟨h0,h1⟩ := comparison_initial_partials_zero hU hz hP hcut hvalue hvelocity hi
    have he : coordinatePoint x a = boxPoint x a := by ext i; fin_cases i <;> simp [coordinatePoint,boxPoint]
    rw [he]
    simp only [energyDensity,h0,h1,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,add_zero,zero_div]
  calc
    _ = ∫ x in xl..xr, (0 : ℝ) := intervalIntegral.integral_congr hpoint
    _ = 0 := intervalIntegral.integral_zero

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonSourceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Taylor SmoothLocal.Hyperbolic

def comparisonSourceBudget (A Cfirst Ctest Ccompare Cres a : ℝ) (ha : 0 < a)
    (N : ℕ) (delta tau epsilon epsilonQ : ℝ) : ℝ :=
  2*A*(pulseLeadingBound a ha*tau^2/tau^N)+
    qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ+Cres/tau^N

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonEnergyScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def comparisonLowerSourceCoefficient (A Cfirst Ctest Ccompare Cres E Q a : ℝ)
    (ha : 0 < a) (delta : ℝ) : ℝ :=
  2*A*(testDensityErrorCoefficient Ctest a ha delta+Ccompare*E)+Cfirst*Q+Cres

theorem comparisonSourceBudget_le_leading
    {A Cfirst Ctest Ccompare Cres E Q a delta tau epsilon epsilonQ : ℝ}
    (ha : 0 < a) (N : ℕ) (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst)
    (hCc : 0 ≤ Ccompare) (hCr : 0 ≤ Cres) (ht : 1 ≤ tau)
    (he : epsilon ≤ E*tau/tau^N) (heQ : epsilonQ ≤ Q*tau/tau^N)
    (hlarge : comparisonLowerSourceCoefficient A Cfirst Ctest Ccompare Cres E Q a ha delta ≤ tau) :
    comparisonSourceBudget A Cfirst Ctest Ccompare Cres a ha N delta tau epsilon epsilonQ ≤
      (2*A*pulseLeadingBound a ha+1)*tau^2/tau^N := by
  have ht0 : 0 < tau := zero_lt_one.trans_le ht
  have hp : 0 < tau^N := pow_pos ht0 N
  have hscale : 0 ≤ tau/tau^N := div_nonneg ht0.le hp.le
  have hrem : qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ ≤
      (2*A*(testDensityErrorCoefficient Ctest a ha delta+Ccompare*E)+Cfirst*Q)*tau/tau^N := by
    have hb := add_le_add
      (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl (testDensityErrorCoefficient Ctest a ha delta*tau/tau^N))
          (mul_le_mul_of_nonneg_left he hCc))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA))
      (mul_le_mul_of_nonneg_left heQ hCf)
    change qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ ≤ _ at hb
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hres : Cres/tau^N ≤ Cres*tau/tau^N := by
    apply div_le_div_of_nonneg_right _ hp.le
    exact le_mul_of_one_le_right hCr ht
  calc
    _ ≤ 2*A*(pulseLeadingBound a ha*tau^2/tau^N)+
        (2*A*(testDensityErrorCoefficient Ctest a ha delta+Ccompare*E)+Cfirst*Q)*tau/tau^N+
        Cres*tau/tau^N := add_le_add (add_le_add le_rfl hrem) hres
    _ = 2*A*(pulseLeadingBound a ha*tau^2/tau^N)+
        comparisonLowerSourceCoefficient A Cfirst Ctest Ccompare Cres E Q a ha delta*(tau/tau^N) := by
      unfold comparisonLowerSourceCoefficient
      ring
    _ ≤ 2*A*(pulseLeadingBound a ha*tau^2/tau^N)+tau*(tau/tau^N) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hlarge hscale)
    _ = _ := by ring

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_QApproximationMargins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem actual_Q_approximation_eventual_margins (Bcompare BQ H : ℝ)
    {d dcompare c a : ℝ} (hd : 0 < d) (hdcompare : 0 < dcompare)
    (hc : 0 < c) (ha : 0 < a) (N : ℕ) (hN : 1 < N) (delta : ℝ) :
    ∀ᶠ tau : ℕ in atTop,
      2 ≤ tau ∧ N ≤ tau ∧
      0 ≤ metricApproximationAccuracy tau ∧ metricApproximationAccuracy tau ≤ 1 ∧
      (4*max Bcompare 0+2)*metricApproximationAccuracy tau ≤ dcompare/2 ∧
      metricApproximationAccuracy tau ≤ (tau : ℝ)/(tau : ℝ)^N ∧
      0 ≤ qPulseFirstJetBudget a ha N delta (tau : ℝ) ∧
      qPulseFirstJetBudget a ha N delta (tau : ℝ) ≤ 1 ∧
      (4*max BQ 0+2)*qPulseFirstJetBudget a ha N delta (tau : ℝ) ≤ d/2 ∧
      H*qPulseFirstJetBudget a ha N delta (tau : ℝ) ≤ c/2 := by
  let K := 4*max Bcompare 0+2
  have hK : 0 < K := by dsimp only [K]; have hh := le_max_right Bcompare 0; linarith
  let epsilon := min 1 (dcompare/(2*K))
  have he : 0 < epsilon := lt_min (by norm_num) (div_pos hdcompare (by positivity))
  obtain ⟨tau0,_,haccurate⟩ := exists_first_error_threshold (by positivity : 0 < 8*epsilon)
  obtain ⟨T,_,hQ⟩ := qPulseFirstJetBudget_eventual_margins BQ H hd hc ha N hN delta
  have hlarge : ∀ᶠ tau : ℕ in atTop, T ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop T)
  filter_upwards [eventually_ge_atTop tau0,eventually_ge_atTop 2,eventually_ge_atTop N,hlarge]
    with tau ht0 ht2 htN ht
  have ht1 : 1 ≤ tau := by omega
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast ht1)
  have herr : metricApproximationAccuracy tau ≤ epsilon := by linarith [haccurate tau ht0]
  have hsmall : K*metricApproximationAccuracy tau ≤ dcompare/2 := by
    have heK : epsilon ≤ dcompare/(2*K) := min_le_right _ _
    have hh := (le_div_iff₀ (show 0 < 2*K by positivity)).mp (herr.trans heK)
    nlinarith
  exact ⟨ht2,htN,(metricApproximationAccuracy_pos (by omega)).le,
    herr.trans (min_le_left _ _),hsmall,
    approximation_budget_le_pulse_error (by omega) ht1 (by omega),
    qPulseFirstJetBudget_nonneg ha N delta htpos.le,(hQ _ ht).1,(hQ _ ht).2.1,(hQ _ ht).2.2⟩

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_PatchTensorRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

def localPatchMetric (g : MetricField) (eta : PatchAddress → SymmetricPerturbation)
    (a : PatchAddress) : MetricField :=
  affinePullbackMetric g (patchAddressCenter a) (patchAddressMatrix a) + perturbationTensor (eta a)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ActualTwoSidedPulseSeparation
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Flow.Reflection
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

theorem exists_uniform_actual_two_sided_pulse_exclusion
    {G Z d c e0 kappa q0 L : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L) ∧
      ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
        ∀ᶠ tau : ℕ in atTop, 1 ≤ tau ∧
          ∀ (g gStar : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
            CapInductionHeight g U Z c e0 z → CapInductionFlow g U G Z d c e0 kappa z Y W →
            |hessianQuotient g z 0-q0| ≤ 1/(100*L) →
            (∀ R : LowerCapRectangle (-r/2), ∀ p ∈ R.image Y,
              testMetric gStar q0 (L*r/16) N delta (tau : ℝ) =ᶠ[𝓝 p] gStar) ∧
            (∀ R : UpperCapRectangle (r/2), ∀ p ∈ R.image Y,
              testMetric gStar q0 (L*r/16) N delta (tau : ℝ) =ᶠ[𝓝 p] gStar) := by
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  obtain ⟨r,hr,hrhalf,hLr,hrsmall⟩ := exists_sectionFour_radius hM hL
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N delta hdelta
  have hevent : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hevent] with tau htau
  have htau0 : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le htau.1
  refine ⟨by exact_mod_cast htau.1,?_⟩
  intro g gStar U W z Y hh hf hcenter
  have hpartial (v : Coord) (hv : v ∈ modelSquare) (i : Fin 2) :
      |coordPartial i (hessianQuotient g z) v| ≤ M := hf.quotientBound [i] (by norm_num) v hv
  constructor
  · intro R p hp
    exact testMetric_eventuallyEq_on_lower_cap hf.quotientSmooth hf.domainOpen hf.squareSubset
      hf.continuous hf.range hf.start hf.ode hh.quotient hM hL hr hpartial hq0 hcenter
      (by linarith : L*r < 2) (by positivity : 0 < L*r/16)
      (by nlinarith [mul_pos hL hr] : L*r/16 ≤ L*r) hrsmall hdelta htau0 htau.2 gStar N R hp
  · intro R p hp
    exact actual_testMetric_eventuallyEq_on_upper_cap hh hf hG hZ hd hc hL hr hLr
      hq0 hcenter hrsmall hdelta htau0 htau.2 gStar N R hp

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_FiniteTaylorComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem taylorApproximation_value (g : MetricField) (a x : ℝ) (u0 u1 : ℝ → ℝ) (N : ℕ) :
    taylorApproximation g a u0 u1 N ![x, a] = u0 x := by
  induction N with
  | zero => exact linearCauchy_value a x u0 u1
  | succ n hn =>
    simp only [taylorApproximation, hn, taylorCorrection, separatedProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    simp [normalizedTimePower]

def comparisonTimePolynomial (g : MetricField) (a : ℝ) (u0 u1 : ℝ → ℝ)
    (x : ℝ) : ℕ → Polynomial ℝ
  | 0 => Polynomial.C (u0 x) + Polynomial.C (u1 x) * (Polynomial.X - Polynomial.C a)
  | n + 1 => comparisonTimePolynomial g a u0 u1 x n +
      Polynomial.C (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n x /
        ((n + 2).factorial : ℝ)) * (Polynomial.X - Polynomial.C a)^(n + 2)

theorem comparisonTimePolynomial_eval (g : MetricField) (a : ℝ) (u0 u1 : ℝ → ℝ)
    (x t : ℝ) (N : ℕ) :
    (comparisonTimePolynomial g a u0 u1 x N).eval t =
      taylorApproximation g a u0 u1 N ![x, t] := by
  induction N with
  | zero => simp [comparisonTimePolynomial, taylorApproximation, linearCauchy]
  | succ n hn =>
    simp only [comparisonTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      hn, taylorApproximation, taylorCorrection, separatedProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, normalizedTimePower]
    ring

theorem comparisonTimePolynomial_natDegree (g : MetricField) (a : ℝ) (u0 u1 : ℝ → ℝ)
    (x : ℝ) (N : ℕ) :
    (comparisonTimePolynomial g a u0 u1 x N).natDegree ≤ N + 1 := by
  induction N with
  | zero =>
    unfold comparisonTimePolynomial
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_sub_C_le a)
  | succ n hn =>
    change (comparisonTimePolynomial g a u0 u1 x n + _).natDegree ≤ n + 1 + 1
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact hn.trans (by omega)
    · apply (Polynomial.natDegree_C_mul_le _ _).trans
      have hp : ((Polynomial.X - Polynomial.C a : Polynomial ℝ)^(n + 2)).natDegree ≤ n + 2 := by
        simpa only [mul_one] using
          (Polynomial.natDegree_pow_le_of_le (n + 2) (Polynomial.natDegree_X_sub_C_le a))
      exact hp.trans (by omega)

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorInitialVelocity
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem taylorApproximation_initial_time_hasDerivAt
    (g : MetricField) (a x : ℝ) (u0 u1 : ℝ → ℝ) (N : ℕ) :
    HasDerivAt (fun t => taylorApproximation g a u0 u1 N ![x,t]) (u1 x) a := by
  induction N with
  | zero =>
    have h := (((hasDerivAt_id a).sub_const a).const_mul (u1 x)).const_add (u0 x)
    change HasDerivAt (fun t => u0 x+u1 x*(t-a)) (u1 x) a
    simpa only [mul_one, id_eq] using h
  | succ n ih =>
    let C := nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n x
    have hc : HasDerivAt (fun t => C*normalizedTimePower a (n+2) t) 0 a := by
      have h := (normalizedTimePower_hasDerivAt a a (n+1)).const_mul C
      simpa only [normalizedTimePower,sub_self,zero_pow (by omega : n+1 ≠ 0),zero_div,mul_zero] using h
    have h := ih.fun_add hc
    change HasDerivAt (fun t => taylorApproximation g a u0 u1 n ![x,t]+
      C*normalizedTimePower a (n+2) t) (u1 x) a
    simpa only [add_zero] using h

theorem taylorApproximation_initial_velocity_of_differentiable
    (g : MetricField) (a x : ℝ) (u0 u1 : ℝ → ℝ) (N : ℕ)
    (hP : DifferentiableAt ℝ (taylorApproximation g a u0 u1 N) ![x,a]) :
    coordPartial 1 (taylorApproximation g a u0 u1 N) ![x,a] = u1 x := by
  have h := hP.hasFDerivAt.comp_hasDerivAt a (verticalPoint_hasDerivAt x a)
  exact h.unique (taylorApproximation_initial_time_hasDerivAt g a x u0 u1 N)

theorem actual_taylor_Cauchy_of_smooth
    (g : MetricField) (z : Coord → ℝ) (a : ℝ) (N : ℕ) {I : Set ℝ}
    (hI : IsOpen I)
    (hP : ContDiffOn ℝ ∞ (taylorApproximation g a (heightCauchyValue z a)
      (heightCauchyVelocity z a) N) (spatialStrip I)) :
    ∀ x ∈ I,
      taylorApproximation g a (heightCauchyValue z a) (heightCauchyVelocity z a) N ![x,a] = z ![x,a] ∧
      coordPartial 1 (taylorApproximation g a (heightCauchyValue z a) (heightCauchyVelocity z a) N) ![x,a] =
        coordPartial 1 z ![x,a] := by
  intro x hx
  refine ⟨taylorApproximation_value g a x _ _ N,?_⟩
  exact taylorApproximation_initial_velocity_of_differentiable g a x _ _ N
    ((hP.contDiffAt ((spatialStrip_isOpen hI).mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

end SmoothLocal.Taylor

end

end OAI
end


