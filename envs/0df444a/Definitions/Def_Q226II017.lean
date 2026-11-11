-- Prove2me | Definitions.Def_Q226II017
-- name    : Q226II017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:57:11.86574+00:00
-- url     : https://prove2.me/theorems/9145612c-98b8-4664-b5fa-f11856d36915
-- title:
--   Definitions bundle Q226II017 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 31 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Caps_BoundedClassCapRadius`, `IsometricImmersion_Caps_BoundedPatchCauchy`, `IsometricImmersion_Caps_FixedRadiusOffPulseCauchy`, `IsometricImmersion_Caps_QPointwiseCauchyJets`, `IsometricImmersion_Coordinates_BoundedPatchSlabGeometry`, `IsometricImmersion_Darboux_QFiniteActual`, `IsometricImmersion_Darboux_QFirstSpatialBounds`, `IsometricImmersion_Darboux_QMetricFirstErrorBound`, `IsometricImmersion_Darboux_QSpatialFiniteInduction`, `IsometricImmersion_Darboux_QSpatialInductionStep`, `IsometricImmersion_Darboux_QSpatialPointwise`, `IsometricImmersion_Darboux_QSpatialRestriction`, `IsometricImmersion_Energy_LocalQResidualL2`, `IsometricImmersion_Estimates_BoundedClassQLow`, `IsometricImmersion_Estimates_FixedRadiusCutBounds`, `IsometricImmersion_Metrics_LocalMetricQActive`, `IsometricImmersion_Pulses_ReferencePulseEdgeInitial`, `IsometricImmersion_Taylor_FiniteTaylorComparison`, `IsometricImmersion_Taylor_TaylorCoefficientBounds`, `IsometricImmersion_Taylor_TaylorJetStability`, `IsometricImmersion_Taylor_TaylorQJetBounds`, `IsometricImmersion_Taylor_TaylorResidual`, `IsometricImmersion_Taylor_UniformTaylorPolynomial`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II014` and `Q226II015` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q226II019`.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 334; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.AbsoluteValue.Basic
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
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
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
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.Count
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Countable
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
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
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_IsometricImmersion
import Definitions.Def_Q226II014
import Definitions.Def_Q226II015

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSpatialRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem qCoordinateChainCoefficient_abs_le_fixedTime_derivative
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hxx : covHessian g z p 0 0 ≠ 0) (w : ChainWord) (r : Fin w.arity → Fin 6)
    (hactive : QActiveComponents w r) :
    |qCoordinateChainCoefficient g z w r p| ≤
      ‖iteratedFDeriv ℝ w.arity (qFixedTimeQ g (p 1)) (qSpatialProjection (qSolutionJet z p))‖ := by
  rw [qCoordinateChainCoefficient_eq_fixedTime hg hU hp hxx w r hactive, ← Real.norm_eq_abs]
  have hb := (iteratedFDeriv ℝ w.arity (qFixedTimeQ g (p 1))
    (qSpatialProjection (qSolutionJet z p))).le_opNorm
      (fun i => Pi.single (qSpatialIndex (r i)) (1 : ℝ))
  simpa only [Pi.norm_single, norm_one, Finset.prod_const_one, mul_one] using hb

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_LocalMetricQActive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_same_region_active_Q_coefficient_bound
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, HorizontalMetricTwoJetBound g p (m + 3) G) →
      CoordinateBound z S 2 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ w ∈ topResidualWords m, ∀ r, QActiveComponents w r → ∀ p ∈ S,
        |qCoordinateChainCoefficient g z w r p| ≤ C := by
  obtain ⟨C, hC, hQ⟩ := exists_local_fixedTime_Q_jet_bound G (max R Z) hG hd hc (m + 3)
  refine ⟨C, hC, ?_⟩
  intro g z U S hg hU hSU hcoords hgB hzB hdet hden w hw r hactive p hp
  have hxx : covHessian g z p 0 0 ≠ 0 := by
    intro he
    have hh := hden p hp
    rw [he, abs_zero] at hh
    linarith
  have he : qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) = qSolutionJet z p :=
    qFixedTimeState_projection (qSolutionJet z p)
  have hpoint : coordinatePoint (qSpatialProjection (qSolutionJet z p) 0) (p 1) = p := point_eta p
  have hbound := hQ g U hg hU (p 1) (qSpatialProjection (qSolutionJet z p))
    (by simpa only [hpoint] using hSU hp)
    (by simpa only [hpoint] using hgB p hp)
    (by rw [he]; exact qSolutionJet_norm_bound_of_coordinateBound hR hzB hcoords hp)
    (by simpa only [hpoint] using hdet p hp)
    (by rw [he, stateQDenominator_qSolutionJet]; exact hden p hp)
    w.arity (q_residual_factor_orders hw r).2
  exact (qCoordinateChainCoefficient_abs_le_fixedTime_derivative hg hU (hSU hp) hxx w r hactive).trans hbound

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QFirstSpatialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_same_region_Q_first_xi_bound
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ Cfirst : ℝ, 0 ≤ Cfirst ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, HorizontalMetricTwoJetBound g p 2 G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ i : Fin 6, i ≠ 1 → ∀ p ∈ S, |coordPartial 0 (heightQCoefficient g z i) p| ≤ Cfirst := by
  obtain ⟨C, hC, hQ⟩ := exists_local_fixedTime_Q_jet_bound G (max R Z) hG hd hc 2
  refine ⟨C * max 1 Z, mul_nonneg hC (zero_le_one.trans (le_max_left _ _)), ?_⟩
  intro g z U S hg hU hz hSU hcoords hgB hzB hdet hden i hi p hp
  have hxx : covHessian g z p 0 0 ≠ 0 := by
    intro he
    have hh := hden p hp
    rw [he, abs_zero] at hh
    linarith
  have he : qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) = qSolutionJet z p :=
    qFixedTimeState_projection (qSolutionJet z p)
  have hpoint : coordinatePoint (qSpatialProjection (qSolutionJet z p) 0) (p 1) = p := point_eta p
  have hz2 : CoordinateBound z S 2 Z := fun ds hds p hp => hzB ds (by omega) p hp
  have hbound := hQ g U hg hU (p 1) (qSpatialProjection (qSolutionJet z p))
    (by simpa only [hpoint] using hSU hp)
    (by simpa only [hpoint] using hgB p hp)
    (by rw [he]; exact qSolutionJet_norm_bound_of_coordinateBound hR hz2 hcoords hp)
    (by simpa only [hpoint] using hdet p hp)
    (by rw [he, stateQDenominator_qSolutionJet]; exact hden p hp) 2 le_rfl
  exact heightQCoefficient_xi_bound_of_fixedTime_second hg hU hz hSU hzB hC hp hxx hbound i hi

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_LocalQResidualL2
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Interval BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_same_slice_actual_Q_source_bound
    (G R Z lengthFloor width : ℝ) (H : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hlen : 0 < lengthFloor)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ B : ℝ≥0, ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ U, covHessian g z p 0 0 ≠ 0) →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, HorizontalMetricTwoJetBound g p (m + 3) G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ theta left right : ℝ,
      (∀ x ∈ Icc left right, coordinatePoint x theta ∈ S) →
      lengthFloor ≤ right - left → right - left ≤ width →
      SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H →
      eLpNorm (fun x => actualQHighRemainder g z m (coordinatePoint x theta)) 2
        (volume.restrict (Icc left right)) ≤ (B : ℝ≥0∞) := by
  obtain ⟨C, hC, hOuter⟩ := exists_same_region_active_Q_coefficient_bound G R Z hG hR hd hc m
  obtain ⟨Cfirst, hCfirst, hFirst⟩ := exists_same_region_Q_first_xi_bound G R Z hG hR hd hc
  let budget := qRemainderSliceBudget C Cfirst lengthFloor 0 width H m
  have hbudget : budget < (⊤ : ℝ≥0∞) := qRemainderSliceBudget_lt_top C Cfirst lengthFloor 0 width H m
  refine ⟨budget.toNNReal, ?_⟩
  intro g z U S hg hU hz hSU hxx hcoords hgB hzB hdet hden theta left right hseg hwidth hupper hL2
  have hz2 : CoordinateBound z S 2 Z := fun ds hds p hp => hzB ds (by omega) p hp
  have houter := hOuter g z U S hg hU hSU hcoords hgB hz2 hdet hden
  have hfirst := hFirst g z U S hg hU hz hSU hcoords
    (fun p hp => (hgB p hp).mono_order (by omega)) hzB hdet hden
  rw [ENNReal.coe_toNNReal hbudget.ne]
  exact (actualQHighRemainder_slice_eLpNorm_two_active hg hU hz hxx
    (fun x hx => hSU (hseg x hx)) hlen hwidth hm hC hCfirst hL2
    (fun w hw r hr x hx => houter w hw r hr _ (hseg x hx))
    (fun x hx => hfirst 2 (by decide) _ (hseg x hx))
    (fun x hx => hfirst 3 (by decide) _ (hseg x hx))).trans
      (qRemainderSliceBudget_mono_width H m hupper)

theorem exists_same_slice_actual_Q_source_norm_bound
    (G R Z lengthFloor width : ℝ) (H : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hlen : 0 < lengthFloor)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ B : ℝ≥0, ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ U, covHessian g z p 0 0 ≠ 0) →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, HorizontalMetricTwoJetBound g p (m + 3) G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ theta left right : ℝ,
      (∀ x ∈ Icc left right, coordinatePoint x theta ∈ S) →
      lengthFloor ≤ right - left → right - left ≤ width →
      SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H →
      Real.sqrt (∫ x in left..right, actualQHighRemainder g z m (coordinatePoint x theta)^2) ≤ (B : ℝ) := by
  obtain ⟨B, hB⟩ := exists_same_slice_actual_Q_source_bound G R Z lengthFloor width H hG hR hlen hd hc m hm
  refine ⟨B, ?_⟩
  intro g z U S hg hU hz hSU hxx hcoords hgB hzB hdet hden theta left right hseg hwidth hupper hL2
  have hn := hB g z U S hg hU hz hSU hxx hcoords hgB hzB hdet hden theta left right hseg hwidth hupper hL2
  have hmem := actualQHighRemainder_slice_memLp_two hg hU hz hxx m (fun x hx => hSU (hseg x hx))
  have hlr : left ≤ right := by linarith
  rw [intervalIntegral.integral_of_le hlr, restrict_Ioc_eq_restrict_Icc,
    sqrt_integral_square_eq_L2_norm hmem, Lp.norm_def, eLpNorm_congr_ae hmem.coeFn_toLp]
  exact ENNReal.toReal_mono (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (B : ℝ≥0∞) ≠ ⊤) hn

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_BoundedClassQLow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

theorem exists_bounded_class_sheared_QLowBounds
    (G R kappa d q0 : ℝ) (M : ℕ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hkappa : 0 < kappa) (hd : 0 < d) (hM : 0 < M) :
    ∃ MQ : ℝ, 0 ≤ MQ ∧ ∀ (g : MetricField) (z : Coord → ℝ) (S : Set Coord),
      BoundedAdmissibleHeight g M z →
      (∀ p ∈ S, inverseShearCoordinates q0 p ∈ modelSquare) →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j k, k ≤ 4 → ∀ p ∈ S,
        ‖iteratedFDeriv ℝ k (fun r => g r i j) (inverseShearCoordinates q0 p)‖ ≤ G) →
      (∀ p ∈ S, d ≤ |(g (inverseShearCoordinates q0 p)).det|) →
      (∀ p ∈ S, gaussianCurvature g (inverseShearCoordinates q0 p) ≤ -kappa / 2) →
      (∀ p ∈ S, |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
        1 / (10 * boundedClassWidth kappa M)) →
      QLowBounds (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) S
        (shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ)) MQ (boundedClassWidth kappa M / 4) := by
  let GS := shearedMetricCoordinateBudget G q0 4
  let ZS := (2 * (1 + |q0|))^3 * (M : ℝ)
  let c := (boundedClassSpeed kappa M)^2 / (2 * (M : ℝ))
  have hGS : 0 ≤ GS := shearedMetricCoordinateBudget_nonneg q0 4 hG
  have hc : 0 < c := boundedClassShearHxxFloor_pos hkappa hM
  obtain ⟨MQ, hMQ, hlow⟩ := exists_actual_QLowBounds GS R ZS hGS hR hd hc
  refine ⟨MQ, hMQ, ?_⟩
  intro g z S hclass hSp hcoords hgB hdet hK hq
  have hclass0 := hclass
  obtain ⟨_, hadm, hjet, _, _⟩ := hclass
  obtain ⟨U, hU, hSU, hg, hz, _, _, _, _⟩ := hadm
  let T : Set Coord := inverseShearCoordinates q0 '' S
  let V : Set Coord := inverseShearCoordinates q0 ⁻¹' U
  have hTU : T ⊆ U := by
    rintro p ⟨r, hr, rfl⟩
    exact hSU (hSp r hr)
  have hSV : S ⊆ V := fun p hp => hSU (hSp p hp)
  have hgCoord : ∀ i j, CoordinateBound (fun p => g p i j) T 4 G := by
    intro i j ds hds p hp
    obtain ⟨r, hr, rfl⟩ := hp
    exact (norm_iteratedCoordPartial_le_jet (hg.1 i j) hU ds (hSU (hSp r hr))).trans
      (hgB i j ds.length hds r hr)
  have hgShear := metric_coordinate_bound_inverse_shear hg hU hTU hG hgCoord q0
  have hgS : ∀ i j, CoordinateBound (fun p => metricInShearCoordinates g q0 p i j) S 4 GS := by
    intro i j ds hds p hp
    exact hgShear i j ds hds p ⟨p, hp, rfl⟩
  have hzCoord : CoordinateBound z modelSquare 3 (M : ℝ) := by
    intro ds hds p hp
    exact (norm_iteratedCoordPartial_le_jet hz hU ds (hSU hp)).trans
      (hjet ds.length (by omega) p hp)
  have hzShear := SmoothLocal.Pulse.CoordinateBound.inverse_shear hzCoord hz hU hSU (Nat.cast_nonneg M) q0
  have hzS : CoordinateBound (heightInShearCoordinates z q0) S 3 ZS := by
    intro ds hds p hp
    exact hzShear ds hds p (hSp p hp)
  have hgSmooth := metricInShearCoordinates_smoothPositive hg q0
  have hVS : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hzSmooth := heightInShearCoordinates_contDiffOn hz q0
  obtain ⟨_, hprincipal⟩ := bounded_class_Q_principal_budgets hclass0 hkappa hG hd hSp
    (fun i j k hk => hgB i j k (by omega)) hdet hK hq
  exact hlow (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) V S
    hgSmooth hVS hzSmooth hSV hcoords hgS hzS
    (fun p hp => by simpa only [metricDet_in_shear_coordinates] using hdet p hp)
    (fun p hp => (hprincipal p hp).1)
    (shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ)) (boundedClassWidth kappa M / 4)
    (fun p hp => (hprincipal p hp).2.1) (fun p hp => (hprincipal p hp).2.2)

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_BoundedClassCapRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

theorem exists_bounded_class_cap_radius_QLowBounds
    (G R kappa d q0 : ℝ) (M : ℕ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hkappa : 0 < kappa) (hd : 0 < d) (hM : 0 < M) (hq0 : |q0| ≤ 1 / 20) :
    ∃ MQ : ℝ, 0 ≤ MQ ∧ ∀ (g : MetricField) (z : Coord → ℝ) (S : Set Coord) (r : ℝ),
      BoundedAdmissibleHeight g M z → 0 ≤ r →
      heightQuotientJetBound G (M : ℝ) d (1 / (M : ℝ)) *
        (r + 107 * (boundedClassWidth kappa M * r) / 100) ≤
          9 / (100 * boundedClassWidth kappa M) →
      (∀ p ∈ S, inverseShearCoordinates q0 p ∈ modelSquare) →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, |p 0| ≤ boundedClassWidth kappa M * r ∧ |p 1| ≤ r) →
      (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun a => g a i j) p‖ ≤ G) →
      (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
      (∀ p ∈ S, gaussianCurvature g (inverseShearCoordinates q0 p) ≤ -kappa / 2) →
      |hessianQuotient g z 0 - q0| ≤ 1 / (100 * boundedClassWidth kappa M) →
      QLowBounds (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) S
        (shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ)) MQ (boundedClassWidth kappa M / 4) := by
  obtain ⟨MQ, hMQ, hlow⟩ := exists_bounded_class_sheared_QLowBounds G R kappa d q0 M hG hR hkappa hd hM
  refine ⟨MQ, hMQ, ?_⟩
  intro g z S r hclass hr hrsmall hSp hcoords haxes hgB hdet hK hcenter
  exact hlow g z S hclass hSp hcoords
    (fun i j k hk p hp => hgB i j k hk _ (hSp p hp))
    (fun p hp => hdet _ (hSp p hp)) hK
    (fun p hp => bounded_class_slab_quotient_small_of_cap_radius hclass hG hd hr hq0 hrsmall
      hgB hdet hcenter (hSp p hp) (haxes p hp).1 (haxes p hp).2)

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSpatialInductionStep
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_Q_spatial_induction_step
    (G R Z s0 M speed xl xr T lengthFloor : ℝ) (H A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ Hnew : ℝ≥0, H ≤ Hnew ∧
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      QLowBounds g z (shrinkingSlab xl xr a b speed) s0 M speed →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (m + 5) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ m + 4 → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      (∀ t ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) t
        (inwardLeft xl a speed t) (inwardRight xr a speed t) (m + 2) H) →
      ∀ t ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) t
        (inwardLeft xl a speed t) (inwardRight xr a speed t) (m + 3) Hnew := by
  obtain ⟨B, hSource⟩ := exists_same_slice_actual_Q_source_norm_bound
    G R Z lengthFloor (xr - xl) H hG hR hlen hd hc m hm
  let I : ℝ≥0 := initialCutEnergyBudget (xr - xl) M A
  let C : ℝ := 8 * (M * (m + 4)) * (1 + 1 / s0)
  have hC : 0 ≤ C := by dsimp [C] <;> positivity
  let Ebound : ℝ≥0 := ⟨Real.exp (C * T) * ((I : ℝ) + T * (B : ℝ)), by positivity⟩
  let Hnew : ℝ≥0 := max H (spatialEnergyNormBudget s0 Ebound)
  refine ⟨Hnew, le_max_left _ _, ?_⟩
  intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords hgB hzB hdet hden hcut hprev t ht
  let S := shrinkingSlab xl xr a b speed
  have hU := coordinateRectangle_isOpen radius lo hi
  have hlength : 2 * speed * (b - a) < xr - xl := by
    have hh := mul_le_mul_of_nonneg_left habT (by positivity : 0 ≤ 2 * speed)
    linarith
  have hSU : S ⊆ coordinateRectangle radius lo hi :=
    shrinkingSlab_subset_rectangle hab hspeed hxl hxr ha hb hlength
  have htime (v : ℝ) (hv : v ∈ Icc a b) : v ∈ Ioo lo hi :=
    ⟨ha.1.trans_le hv.1, hv.2.trans_lt hb.2⟩
  have hgeo (v : ℝ) (hv : v ∈ Icc a b) := inward_interval_geometry hab hspeed hxl hxr hlength hv
  have hsource (v : ℝ) (hv : v ∈ Icc a b) :
      movingSourceNorm xl xr a speed (actualQHighRemainder g z m) v ≤ (B : ℝ) := by
    have hwlow : lengthFloor ≤ inwardRight xr a speed v - inwardLeft xl a speed v := by
      unfold inwardRight inwardLeft
      have hvT : v - a ≤ T := (sub_le_sub_right hv.2 a).trans habT
      have hmul := mul_le_mul_of_nonneg_left hvT (by positivity : 0 ≤ 2 * speed)
      linarith
    have hwup : inwardRight xr a speed v - inwardLeft xl a speed v ≤ xr - xl := by
      unfold inwardRight inwardLeft
      have hh : 0 ≤ speed * (v - a) := mul_nonneg hspeed (sub_nonneg.mpr hv.1)
      linarith
    exact hSource g z (coordinateRectangle radius lo hi) S hg hU hz hSU hxx hcoords
      (fun p hp => coordinateMetricBound_to_horizontalTwoJet hgB hp)
      (hzB.mono (by norm_num) le_rfl) hdet hden v
      (inwardLeft xl a speed v) (inwardRight xr a speed v)
      (fun x hx => point_mem_shrinkingSlab hv hx) hwlow hwup (hprev v hv)
  have hS := heightQCoefficient_contDiffOn hg hU hz hxx 5
  have hInitial : Real.sqrt (∫ x in xl..xr,
      energyDensity (heightQCoefficient g z 5) (horizontalJet z (m + 3)) (coordinatePoint x a)) ≤ (I : ℝ) := by
    have hcutPoint (x : ℝ) (hx : x ∈ Icc xl xr) : coordinatePoint x a ∈ S := by
      apply point_mem_shrinkingSlab (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
      simpa only [inwardLeft, inwardRight, sub_self, mul_zero, add_zero, sub_zero] using hx
    apply initial_energy_bound_of_cut_jets hU hz hS
      (fun x hx => hSU (hcutPoint x hx))
      (by nlinarith [mul_nonneg hspeed (sub_nonneg.mpr hab)]) hM
      (fun x hx => (le_abs_self _).trans (hLow _ (hcutPoint x hx)).2.2.2.1) (m + 3) A
    simpa only [Nat.add_assoc] using hcut
  have hEt : Real.sqrt (movingEnergy xl xr a speed (heightQCoefficient g z 5)
      (horizontalJet z (m + 3)) t) ≤ (Ebound : ℝ) := by
    have httop : shrinkingSlab xl xr a t speed ⊆ S := shrinkingSlab_mono_top ht.2
    have hlenT : 2 * speed * (t - a) < xr - xl := by
      have hh := mul_le_mul_of_nonneg_left ht.2 (by positivity : 0 ≤ 2 * speed)
      nlinarith
    have hprop := actual_Q_moving_slab_energy hg hz hD hxx m hradius ht.1 hspeed
      hxl hxr ha (htime t ht) hlenT hs0 (by positivity : 0 ≤ M * (m + 4))
      (fun p hp => (hLow p (httop hp)).1)
      (fun p hp => by simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc,
          show (3 : ℝ) + 1 = 4 by norm_num] using
        hLow.high_coefficients hM (m + 3) (httop hp))
      (fun p hp => (hLow p (httop hp)).2.2.2.2.2.2.2)
    have hR := actualQHighRemainder_contDiffOn hg hU hz hD hxx m
    have hforceCont : ContinuousOn (movingSourceNorm xl xr a speed (actualQHighRemainder g z m)) (Icc a t) :=
      movingSourceNorm_continuousOn hR hradius
        (fun v hv => (hgeo v ⟨hv.1, hv.2.trans ht.2⟩).1)
        (fun v hv => (hgeo v ⟨hv.1, hv.2.trans ht.2⟩).2.1)
        (fun v hv => htime v ⟨hv.1, hv.2.trans ht.2⟩)
    have hInt : (∫ v in a..t, movingSourceNorm xl xr a speed (actualQHighRemainder g z m) v) ≤
        (t - a) * (B : ℝ) := by
      have hh : (∫ v in a..t, movingSourceNorm xl xr a speed (actualQHighRemainder g z m) v) ≤
          ∫ v in a..t, (B : ℝ) := intervalIntegral.integral_mono_on ht.1
        (hforceCont.intervalIntegrable_of_Icc ht.1) intervalIntegrable_const
        (fun v hv => hsource v ⟨hv.1, hv.2.trans ht.2⟩)
      simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh
    have hduration : 0 ≤ t - a := sub_nonneg.mpr ht.1
    have hdurationT : t - a ≤ T := (sub_le_sub_right ht.2 a).trans habT
    have hfirst : Real.sqrt (movingEnergy xl xr a speed (heightQCoefficient g z 5)
        (horizontalJet z (m + 3)) t) ≤ Real.exp (C * (t - a)) * ((I : ℝ) + (t - a) * (B : ℝ)) :=
      hprop.trans (mul_le_mul_of_nonneg_left (add_le_add hInitial hInt) (Real.exp_pos _).le)
    exact hfirst.trans (mul_le_mul
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdurationT hC))
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hdurationT B.2))
      (by positivity) (Real.exp_pos _).le)
  intro i n hn
  by_cases hsmall : n ≤ m + 2
  · exact (hprev t ht i n hsmall).trans (by exact_mod_cast (le_max_left H (spatialEnergyNormBudget s0 Ebound)))
  · have he : n = m + 3 := by omega
    subst n
    have hn := spatialFirstJet_slice_eLpNorm_two_of_energy hU hz hS
      (fun x hx => hSU (point_mem_shrinkingSlab ht hx))
      (hgeo t ht).2.2.1.le hs0
      (fun x hx => (hLow _ (point_mem_shrinkingSlab ht hx)).1) (m + 3) Ebound hEt i
    exact hn.trans (by exact_mod_cast (le_max_right H (spatialEnergyNormBudget s0 Ebound)))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSpatialFiniteInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_Q_spatial_induction_offset
    (G R Z s0 M speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∀ k : ℕ, ∃ H : ℝ≥0,
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      QLowBounds g z (shrinkingSlab xl xr a b speed) s0 M speed →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (k + 9) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ k + 8 → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) t
        (inwardLeft xl a speed t) (inwardRight xr a speed t) (k + 7) H := by
  intro k
  induction k with
  | zero =>
      refine ⟨firstJetSliceBudget Z (xr - xl), ?_⟩
      intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
        hLow hcoords hgB hzB hdet hden hcut t ht
      apply coordinateC8_to_spatialFirstJet_L2_seven hzB hZ
        (fun x hx => point_mem_shrinkingSlab ht hx)
      unfold inwardLeft inwardRight
      have hh : 0 ≤ speed * (t - a) := mul_nonneg hspeed (sub_nonneg.mpr ht.1)
      linarith
  | succ k ih =>
      obtain ⟨Hprev, hprev⟩ := ih
      obtain ⟨Hnew, hle, hstep⟩ := exists_Q_spatial_induction_step
        G R Z s0 M speed xl xr T lengthFloor Hprev A hG hR hs0 hM hspeed hT hlen hwidth
        hd hc (k + 5) (by omega)
      refine ⟨Hnew, ?_⟩
      intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
        hLow hcoords hgB hzB hdet hden hcut t ht
      have hold : ∀ v ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) v
          (inwardLeft xl a speed v) (inwardRight xr a speed v) (k + 7) Hprev :=
        hprev g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
          hLow hcoords (fun i j => (hgB i j).mono (by omega) le_rfl) hzB hdet hden
          (fun ds hds x hx => hcut ds (by omega) x hx)
      have hnew := hstep g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
        hLow hcoords (fun i j => (hgB i j).mono (by omega) le_rfl) hzB hdet hden
        (fun ds hds x hx => hcut ds (by omega) x hx)
        (by simpa only [Nat.add_assoc] using hold) t ht
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hnew

theorem exists_finite_Q_spatial_bound
    (G R Z s0 M speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ H : ℝ≥0,
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      QLowBounds g z (shrinkingSlab xl xr a b speed) s0 M speed →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (max 9 (N + 2)) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (N + 1) → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) t
        (inwardLeft xl a speed t) (inwardRight xr a speed t) N H := by
  obtain ⟨H, hH⟩ := exists_Q_spatial_induction_offset
    G R Z s0 M speed xl xr T lengthFloor A hG hR hZ hs0 hM hspeed hT hlen hwidth hd hc (N - 7)
  refine ⟨H, ?_⟩
  intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords hgB hzB hdet hden hcut t ht
  have hmetricOrder : N - 7 + 9 ≤ max 9 (N + 2) := by omega
  have hcutOrder : N - 7 + 8 ≤ max 8 (N + 1) := by omega
  have hb := hH g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords (fun i j => (hgB i j).mono hmetricOrder le_rfl) hzB hdet hden
    (fun ds hds x hx => hcut ds (hds.trans hcutOrder) x hx) t ht
  exact SpatialSliceL2Bound.mono_order_budget hb (by omega) le_rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSpatialPointwise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_finite_Q_spatial_pointwise_bound
    (G R Z s0 M speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      QLowBounds g z (shrinkingSlab xl xr a b speed) s0 M speed →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (max 9 (N + 3)) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (N + 2) → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, ∀ x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t),
        ∀ i : Fin 2, ∀ n ≤ N,
          |spatialJet (spatialFirstJet z i) n (coordinatePoint x t)| ≤ B := by
  obtain ⟨H, hH⟩ := exists_finite_Q_spatial_bound
    G R Z s0 M speed xl xr T lengthFloor A hG hR hZ hs0 hM hspeed hT hlen hwidth hd hc (N + 1)
  refine ⟨Real.sqrt (2 + 1 / lengthFloor) * (H : ℝ), by positivity, ?_⟩
  intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords hgB hzB hdet hden hcut t ht x hx i n hn
  have hnorm := hH g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords (fun i j => (hgB i j).mono (by omega) le_rfl) hzB hdet hden
    (fun ds hds x hx => hcut ds (by omega) x hx) t ht
  have hU := coordinateRectangle_isOpen radius lo hi
  have hlength : 2 * speed * (b - a) < xr - xl := by
    have hh := mul_le_mul_of_nonneg_left habT (by positivity : 0 ≤ 2 * speed)
    linarith
  have hSU := shrinkingSlab_subset_rectangle hab hspeed hxl hxr ha hb hlength
  have hlength_t : lengthFloor ≤ inwardRight xr a speed t - inwardLeft xl a speed t := by
    unfold inwardLeft inwardRight
    have hd : t - a ≤ T := (sub_le_sub_right ht.2 a).trans habT
    have hh := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2 * speed)
    linarith
  exact hnorm.pointwise_below_top hU (fun j => partial_contDiffOn hz hU j)
    (fun y hy => hSU (point_mem_shrinkingSlab ht hy)) hlen hlength_t i n (Nat.succ_le_succ hn) hx

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QFiniteActual
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_finite_actual_Q_spatial_pointwise_bound
    (G R Z s0 speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      (∀ p ∈ shrinkingSlab xl xr a b speed, s0 ≤ heightQCoefficient g z 5 p) →
      (∀ p ∈ shrinkingSlab xl xr a b speed,
        |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (max 9 (N + 3)) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (N + 2) → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, ∀ x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t),
        ∀ i : Fin 2, ∀ n ≤ N,
          |spatialJet (spatialFirstJet z i) n (coordinatePoint x t)| ≤ B := by
  obtain ⟨M, hM, hlow⟩ := exists_actual_QLowBounds G R Z hG hR hd hc
  obtain ⟨B, hB, hbound⟩ := exists_finite_Q_spatial_pointwise_bound
    G R Z s0 M speed xl xr T lengthFloor A hG hR hZ hs0 hM hspeed hT hlen hwidth hd hc N
  refine ⟨B, hB, ?_⟩
  intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hs hchar hcoords hgB hzB hdet hden hcut
  have hlength : 2 * speed * (b - a) < xr - xl := by
    have hh := mul_le_mul_of_nonneg_left habT (by positivity : 0 ≤ 2 * speed)
    linarith
  have hSU := shrinkingSlab_subset_rectangle hab hspeed hxl hxr ha hb hlength
  have hLow := hlow g z (coordinateRectangle radius lo hi) (shrinkingSlab xl xr a b speed)
    hg (coordinateRectangle_isOpen radius lo hi) hz hSU hcoords
    (fun i j => (hgB i j).mono (by omega) le_rfl)
    (hzB.mono (by norm_num) le_rfl) hdet hden s0 speed hs hchar
  exact hbound g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords hgB hzB hdet hden hcut

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorJetStability
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

theorem sixVariableQ_taylorCorrection_time_jets
    {g : MetricField} {U : Set Coord} {P : Coord → ℝ} {C : ℝ → ℝ} {I : Set ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ I)
    (hp : (![x, a] : Coord) ∈ U) (hxx : covHessian g P ![x, a] 0 0 ≠ 0) :
    ∀ k ≤ n,
      iteratedDeriv k (fun t => sixVariableQ g (qSolutionJet
        (fun q => P q + taylorCorrection C a n q) ![x, t])) a =
      iteratedDeriv k (fun t => sixVariableQ g (qSolutionJet P ![x, t])) a := by
  intro k hk
  have hnew := hP.add (taylorCorrection_contDiffOn hC a n)
  have hj := qSolutionJet_taylorCorrection_time_jets hI hP hC a n hx
  have hvalue : qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, a] =
      qSolutionJet P ![x, a] := by simpa only [iteratedDeriv_zero] using hj 0 (by omega)
  have hQ := sixVariableQ_contDiffAt_solutionJet hg hU hp hxx
  rw [← hvalue] at hQ
  exact iteratedDeriv_comp_eq_of_jets (Q := sixVariableQ g)
    (qSolutionJet_time_slice_contDiffAt hI hnew hx a)
    (qSolutionJet_time_slice_contDiffAt hI hP hx a) hQ
    (fun j hjk => hj j (hjk.trans hk))

end SmoothLocal.Taylor

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

theorem nextTaylorCoefficient_eq_residual_jet {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) (a : ℝ) (n : ℕ)
    {x : ℝ} (hx : x ∈ I) (hp : (![x, a] : Coord) ∈ U)
    (hxx : covHessian g P ![x, a] 0 0 ≠ 0) :
    nextTaylorCoefficient g a P n x =
      -iteratedDeriv n (fun t => qResidual g P ![x, t]) a := by
  exact congrArg Neg.neg (verticalJet_slice (comparisonDomain_isOpen hg hU hI hP)
    (qResidual_contDiffOn hg hU hI hP) x n a (mem_comparisonDomain hx hp hxx)).symm

theorem qResidual_taylorCorrection_time_jet
    {g : MetricField} {U : Set Coord} {P : Coord → ℝ} {C : ℝ → ℝ} {I : Set ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n k : ℕ) (hk : k ≤ n)
    {x : ℝ} (hx : x ∈ I) (hp : (![x, a] : Coord) ∈ U)
    (hxx : covHessian g P ![x, a] 0 0 ≠ 0) :
    iteratedDeriv k (fun t => qResidual g
      (fun q => P q + taylorCorrection C a n q) ![x, t]) a =
      iteratedDeriv k (fun t => qResidual g P ![x, t]) a +
        if k = n then C x else 0 := by
  have hV := spatialStrip_isOpen hI
  have hR := taylorCorrection_contDiffOn hC a n
  have hnew := hP.add hR
  have htt : ContDiffAt ℝ ∞ (fun t => coordPartial 1 (coordPartial 1 P) ![x, t]) a :=
    ((partial_contDiffOn (partial_contDiffOn hP hV 1) hV 1).contDiffAt
      (hV.mem_nhds hx)).comp a (verticalPoint_contDiff x).contDiffAt
  have httnew : ContDiffAt ℝ ∞ (fun t => coordPartial 1 (coordPartial 1
      (fun q => P q + taylorCorrection C a n q)) ![x, t]) a :=
    ((partial_contDiffOn (partial_contDiffOn hnew hV 1) hV 1).contDiffAt
      (hV.mem_nhds hx)).comp a (verticalPoint_contDiff x).contDiffAt
  have hQouter := sixVariableQ_contDiffAt_solutionJet hg hU hp hxx
  have hQ : ContDiffAt ℝ ∞ (fun t => sixVariableQ g (qSolutionJet P ![x, t])) a :=
    ContDiffAt.comp (g := sixVariableQ g) (f := fun t => qSolutionJet P ![x, t])
      a hQouter (qSolutionJet_time_slice_contDiffAt hI hP hx a)
  have hstate : qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, a] =
      qSolutionJet P ![x, a] := by
    simpa only [iteratedDeriv_zero] using
      qSolutionJet_taylorCorrection_time_jets hI hP hC a n hx 0 (Nat.zero_le n)
  have hQouterNew : ContDiffAt ℝ ∞ (sixVariableQ g)
      (qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, a]) := by
    rw [hstate]
    exact hQouter
  have hQnew : ContDiffAt ℝ ∞ (fun t => sixVariableQ g
      (qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, t])) a :=
    ContDiffAt.comp (g := sixVariableQ g)
      (f := fun t => qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, t])
      a hQouterNew (qSolutionJet_time_slice_contDiffAt hI hnew hx a)
  have he : (fun t => coordPartial 1 (coordPartial 1
      (fun q => P q + taylorCorrection C a n q)) ![x, t]) =
      (fun t => coordPartial 1 (coordPartial 1 P) ![x, t] +
        C x * normalizedTimePower a n t) := by
    funext t
    rw [secondCoordPartial_add hV hP hR (p := ![x, t]) hx 1 1,
      taylorCorrection_partial_tt hC hI a n (p := ![x, t]) hx]
    rfl
  have hmon : ContDiffAt ℝ ∞ (fun t => C x * normalizedTimePower a n t) a :=
    (contDiff_const.mul (normalizedTimePower_contDiff a n)).contDiffAt
  change iteratedDeriv k (fun t =>
    coordPartial 1 (coordPartial 1 (fun q => P q + taylorCorrection C a n q)) ![x, t] -
      sixVariableQ g (qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, t])) a =
    iteratedDeriv k (fun t => coordPartial 1 (coordPartial 1 P) ![x, t] -
      sixVariableQ g (qSolutionJet P ![x, t])) a + _
  rw [iteratedDeriv_fun_sub (httnew.of_le (WithTop.coe_le_coe.mpr le_top))
      (hQnew.of_le (WithTop.coe_le_coe.mpr le_top)),
    iteratedDeriv_fun_sub (htt.of_le (WithTop.coe_le_coe.mpr le_top))
      (hQ.of_le (WithTop.coe_le_coe.mpr le_top)),
    sixVariableQ_taylorCorrection_time_jets hg hU hI hP hC a n hx hp hxx k hk,
    he, iteratedDeriv_fun_add (htt.of_le (WithTop.coe_le_coe.mpr le_top))
      (hmon.of_le (WithTop.coe_le_coe.mpr le_top)), coefficient_timePower_jet]
  ring

theorem nextTaylorCoefficient_cancels
    {g : MetricField} {U : Set Coord} {P : Coord → ℝ} {I : Set ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) (a : ℝ) (n : ℕ)
    (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U)
    (hxx : ∀ x ∈ I, covHessian g P ![x, a] 0 0 ≠ 0)
    (hzero : ∀ x ∈ I, ∀ k < n, iteratedDeriv k (fun t => qResidual g P ![x, t]) a = 0) :
    ∀ x ∈ I, ∀ k < n + 1,
      iteratedDeriv k (fun t => qResidual g
        (fun q => P q + taylorCorrection (nextTaylorCoefficient g a P n) a n q) ![x, t]) a = 0 := by
  intro x hx k hk
  rw [qResidual_taylorCorrection_time_jet hg hU hI hP
    (nextTaylorCoefficient_contDiffOn hg hU hI hP a n hcut hxx)
    a n k (by omega) hx (hcut x hx) (hxx x hx)]
  by_cases hkn : k = n
  · subst k
    rw [ite_eq_left rfl, nextTaylorCoefficient_eq_residual_jet hg hU hI hP a n
      hx (hcut x hx) (hxx x hx)]
    ring
  · rw [ite_eq_right hkn, hzero x hx k (by omega), zero_add]

end SmoothLocal.Taylor

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

theorem taylorApproximation_properties {g : MetricField} {U : Set Coord}
    {u0 u1 : ℝ → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I)
    (a : ℝ) (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U)
    (hxx : ∀ x ∈ I, covHessian g (linearCauchy a u0 u1) ![x, a] 0 0 ≠ 0) :
    ∀ N,
      ContDiffOn ℝ ∞ (taylorApproximation g a u0 u1 N) (spatialStrip I) ∧
      (∀ x ∈ I, qSolutionJet (taylorApproximation g a u0 u1 N) ![x, a] =
        qSolutionJet (linearCauchy a u0 u1) ![x, a]) ∧
      (∀ x ∈ I, ∀ k < N,
        iteratedDeriv k (fun t => qResidual g (taylorApproximation g a u0 u1 N) ![x, t]) a = 0) := by
  intro N
  induction N with
  | zero =>
    refine ⟨linearCauchy_contDiffOn h0 h1 a, fun _ _ => rfl, ?_⟩
    intro _ _ k hk
    omega
  | succ n hn =>
    have hxxn : ∀ x ∈ I,
        covHessian g (taylorApproximation g a u0 u1 n) ![x, a] 0 0 ≠ 0 := by
      intro x hx
      rw [← stateQDenominator_qSolutionJet, hn.2.1 x hx, stateQDenominator_qSolutionJet]
      exact hxx x hx
    have hC := nextTaylorCoefficient_contDiffOn hg hU hI hn.1 a n hcut hxxn
    refine ⟨hn.1.add (taylorCorrection_contDiffOn hC a n), ?_, ?_⟩
    · intro x hx
      have hj := qSolutionJet_taylorCorrection_time_jets hI hn.1 hC a n hx 0 (Nat.zero_le n)
      change qSolutionJet (fun p => taylorApproximation g a u0 u1 n p +
        taylorCorrection (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) a n p)
        ![x, a] = _
      have hj0 : qSolutionJet (fun p => taylorApproximation g a u0 u1 n p +
          taylorCorrection (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) a n p)
          ![x, a] = qSolutionJet (taylorApproximation g a u0 u1 n) ![x, a] := by
        simpa only [iteratedDeriv_zero] using hj
      exact hj0.trans (hn.2.1 x hx)
    · exact nextTaylorCoefficient_cancels hg hU hI hn.1 a n hcut hxxn hn.2.2

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_QPointwiseCauchyJets
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix NNReal

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.ODE
open SmoothLocal.Weighted SmoothLocal.Hyperbolic

theorem exists_finite_actual_Q_cauchy_fullJet_bound
    (G R Z s0 speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2*speed*T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b-a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      (∀ p ∈ shrinkingSlab xl xr a b speed, s0 ≤ heightQCoefficient g z 5 p) →
      (∀ p ∈ shrinkingSlab xl xr a b speed,
        |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (max 9 (N+3)) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (N+2) → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, ∀ x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t),
        ∀ n ≤ N,
          ‖iteratedFDeriv ℝ n (heightCauchyValue z t) x‖ ≤ B ∧
          ‖iteratedFDeriv ℝ n (heightCauchyVelocity z t) x‖ ≤ B := by
  obtain ⟨B0, _, hpoint⟩ := exists_finite_actual_Q_spatial_pointwise_bound
    G R Z s0 speed xl xr T lengthFloor A hG hR hZ hs0 hspeed hT hlen hwidth hd hc N
  refine ⟨max Z B0, hZ.trans (le_max_left _ _), ?_⟩
  intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hs hchar hcoords hgB hzB hdet hden hcut t ht x hx n hn
  have hU := coordinateRectangle_isOpen radius lo hi
  have hlength : 2*speed*(b-a) < xr-xl := by
    have hh := mul_le_mul_of_nonneg_left habT (by positivity : 0 ≤ 2*speed)
    linarith
  have hSU := shrinkingSlab_subset_rectangle hab hspeed hxl hxr ha hb hlength
  have hpS := point_mem_shrinkingSlab ht hx
  have hp := hSU hpS
  have hv : |z (coordinatePoint x t)| ≤ Z := hzB [] (by norm_num) _ hpS
  exact cauchy_fullJets_of_actual_spatial_firstJets hz hU hp hv
    (hpoint g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
      hs hchar hcoords hgB hzB hdet hden hcut t ht x hx) n hn

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_BoundedPatchSlabGeometry
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_bounded_patch_actual_slab_QLowBounds
    (G kappa d q0 : ℝ) (M : ℕ) (hG : 0 ≤ G)
    (hkappa : 0 < kappa) (hd : 0 < d) (hM : 0 < M) (hq0 : |q0| ≤ 1 / 20) :
    ∃ MQ : ℝ, 0 ≤ MQ ∧ ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa)
      (z : Coord → ℝ) (r b : ℝ),
      BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z → 0 ≤ r → b ≤ 0 →
      boundedClassWidth kappa M * r ≤ 1 / 20 →
      heightQuotientJetBound G (M : ℝ) d (1 / (M : ℝ)) *
        (r + 107 * (boundedClassWidth kappa M * r) / 100) ≤
          9 / (100 * boundedClassWidth kappa M) →
      (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
      (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
      |hessianQuotient (perturbedMetric g0 eta.val) z 0 - q0| ≤
        1 / (100 * boundedClassWidth kappa M) →
      QLowBounds (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
        (heightInShearCoordinates z q0)
        (shrinkingSlab (-(boundedClassWidth kappa M * r)) (boundedClassWidth kappa M * r)
          (-r) b (boundedClassWidth kappa M / 4))
        (shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ)) MQ (boundedClassWidth kappa M / 4) := by
  obtain ⟨MQ, hMQ, hlow⟩ := exists_bounded_class_cap_radius_QLowBounds
    G 1 kappa d q0 M hG (by norm_num) hkappa hd hM hq0
  refine ⟨MQ, hMQ, ?_⟩
  intro g0 eta z r b hclass hr hb hLr hrsmall hgB hdet hcenter
  let S := shrinkingSlab (-(boundedClassWidth kappa M * r)) (boundedClassWidth kappa M * r)
    (-r) b (boundedClassWidth kappa M / 4)
  have haxes (p : Coord) (hp : p ∈ S) := shrinking_class_slab_axis_bounds hr hb hp
  have hcentral (p : Coord) (hp : p ∈ S) := actual_patch_curvature_on_class_slab eta hr hb hLr hq0 hp
  have hrsmall' : r ≤ 1 / 20 := by
    have hL : 1 ≤ boundedClassWidth kappa M :=
      (by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M)
    have hh : r ≤ boundedClassWidth kappa M * r := by nlinarith
    exact hh.trans hLr
  exact hlow (perturbedMetric g0 eta.val) z S r hclass hr hrsmall
    (fun p hp => centralBox_subset_modelSquare (hcentral p hp).1)
    (fun p hp => ⟨by linarith [(haxes p hp).1], by linarith [(haxes p hp).2]⟩)
    haxes hgB hdet (fun p hp => (hcentral p hp).2.le) hcenter

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_BoundedPatchCauchy
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix NNReal

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_bounded_patch_cauchy_bound
    (G d kappa q0 r C : ℝ) (M : ℕ) (A : ℝ≥0) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hr : 0 < r) (hrhalf : r < 1/2)
    (hC : 0 ≤ C) (hq0 : |q0| ≤ 1/20)
    (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M)) (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa)
      (z : Coord → ℝ) (b : ℝ),
      BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z → -r ≤ b → b ≤ 0 →
      (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
      (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
      |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
      (∀ i j, CoordinateBound (fun p => metricInShearCoordinates (perturbedMetric g0 eta.val) q0 p i j)
        (shrinkingSlab (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r)
          (-r) b (boundedClassWidth kappa M/4)) (max 9 (K+3)) C) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (K+2) → ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r →
        |iteratedCoordPartial ds (heightInShearCoordinates z q0) (coordinatePoint x (-r))| ≤ (A : ℝ)) →
      ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
        ‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0) b) x‖ ≤ B ∧
        ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0) b) x‖ ≤ B := by
  let L := boundedClassWidth kappa M
  let Zs := (2*(1+|q0|))^8*(M : ℝ)
  let s0 := shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ)
  let c0 := (boundedClassSpeed kappa M)^2/(2*(M : ℝ))
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hZs : 0 ≤ Zs := by dsimp [Zs] <;> positivity
  have hs0 : 0 < s0 := shearedQPositiveFloor_pos q0 hG (Nat.cast_nonneg M) hd (Nat.cast_pos.mpr hM)
  have hc0 : 0 < c0 := boundedClassShearHxxFloor_pos hkappa hM
  obtain ⟨B,hB,hpoint⟩ := exists_finite_actual_Q_cauchy_fullJet_bound
    C 1 Zs s0 (L/4) (-(L*r)) (L*r) r (L*r) A hC (by norm_num) hZs hs0
      (by positivity) hr.le (mul_pos hL hr) (by nlinarith [mul_pos hL hr]) hd hc0 K
  obtain ⟨_,_,hlow⟩ := exists_bounded_patch_actual_slab_QLowBounds
    G kappa d q0 M hG hkappa hd hM hq0
  refine ⟨B,hB,?_⟩
  intro g0 eta z b hclass hab hb hgB hdet hcenter hmetric hcut x hx n hn
  let g := perturbedMetric g0 eta.val
  let gs := metricInShearCoordinates g q0
  let zs := heightInShearCoordinates z q0
  let S := shrinkingSlab (-(L*r)) (L*r) (-r) b (L/4)
  have hQ := hlow g0 eta z r b hclass hr.le hb hLr hrsmall hgB hdet hcenter
  have haxes (p : Coord) (hp : p ∈ S) := shrinking_class_slab_axis_bounds hr.le hb hp
  have hcentral (p : Coord) (hp : p ∈ S) := actual_patch_curvature_on_class_slab eta hr.le hb hLr hq0 hp
  have hSp (p : Coord) (hp : p ∈ S) : inverseShearCoordinates q0 p ∈ modelSquare :=
    centralBox_subset_modelSquare (hcentral p hp).1
  have hSbox : S ⊆ closedRectangle (-(L*r)) (L*r) (-r) b := by
    intro p hp
    exact ⟨abs_le.mp (haxes p hp).1,hp.1⟩
  obtain ⟨radius,lo,hi,hradius,hlo,hhi,hgs,hzs,hD,hxx⟩ :=
    exists_actual_patch_Q_rectangle eta hclass hG hd hkappa hr hab hb hLr hq0 hrsmall hgB hdet hcenter
  obtain ⟨U,hU,hSU,_,hz,_,_,_,_⟩ := hclass.2.1
  have hZbase : CoordinateBound z modelSquare 8 (M : ℝ) :=
    coordinateBound_of_frechet_bounds hz hU hSU hclass.2.2.1
  have hZshear := SmoothLocal.Pulse.CoordinateBound.inverse_shear
    hZbase hz hU hSU (Nat.cast_nonneg M) q0
  have hzB : CoordinateBound zs S 8 Zs := by
    intro ds hds p hp
    exact hZshear ds hds p (hSp p hp)
  have hdetS (p : Coord) (hp : p ∈ S) : d ≤ |(gs p).det| := by
    rw [metricDet_in_shear_coordinates]
    exact hdet _ (hSp p hp)
  have hdenS (p : Coord) (hp : p ∈ S) : c0 ≤ |covHessian gs zs p 0 0| :=
    (actual_patch_closed_strip_Hxx_floor eta hclass hG hd hkappa hr.le hb hLr hq0 hrsmall
      hgB hdet hcenter (hSbox hp)).2
  have hcoords (p : Coord) (hp : p ∈ S) : |p 0| ≤ 1 ∧ |p 1| ≤ 1 :=
    ⟨(haxes p hp).1.trans (hLr.trans (by norm_num)),
      (haxes p hp).2.trans (by linarith)⟩
  have hbound := hpoint gs zs radius lo hi (-r) b hgs hzs hD hxx
    ((mul_pos hL hr).trans hradius) hab (by linarith)
    (by linarith) hradius ⟨hlo,hab.trans_lt hhi⟩ ⟨hlo.trans_le hab,hhi⟩
    (fun p hp => (hQ p hp).1)
    (fun p hp => (hQ p hp).2.2.2.2.2.2.2) hcoords hmetric hzB hdetS hdenS
    (fun ds hds x hx => hcut ds hds x (abs_le.mpr hx))
    b ⟨hab,le_rfl⟩ x (halfWidth_mem_inward_interval hL hr ⟨hab,hb⟩ hx) n hn
  exact hbound

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_FixedRadiusCutBounds
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Analytic

theorem exists_actual_finite_lower_cut_bound_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L r : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L))
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop,
        ∀ (gTau : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
          SmoothPositiveOn gTau U → IsOpen U →
          (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) →
          CapInductionHeight gTau U Z c e0 z →
          CapInductionFlow gTau U G Z d c e0 kappa z Y W →
          |hessianQuotient gTau z 0-q0| ≤ 1/(100*L) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
              testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          ∀ ds : List (Fin 2), ds.length ≤ n → ∀ x : ℝ, |x| ≤ L*r →
            |iteratedCoordPartial ds z (inverseShearCoordinates q0 (boxPoint x (-r)))| ≤ C := by
  let m := max 8 (n+3)
  obtain ⟨Bstar,_,hbase⟩ := fixed_metric_finite_coefficient_jet_bound hgStar hV hSV m
  let R := lowerCutRectangle L r hL hr hrhalf hLr
  let J : CapMetricJetBudget (-r/2) := fun _ _ => Bstar+1
  obtain ⟨C,hC,hheight⟩ := uniform_finite_varying_lowerCap_pointwise
    G Z d c e0 kappa hG hZ hd hc J n R (fun _ _ => by dsimp [J] <;> linarith)
  refine ⟨C,hC,?_⟩
  intro N delta hdelta
  have hevent : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hevent,eventually_ge_atTop m] with tau hwidth hm
  intro gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happrox ds hds x hx
  have htau0 : (0 : ℝ) < tau := zero_lt_one.trans_le hwidth.1
  have htau1 : 1 ≤ tau := by exact_mod_cast hwidth.1
  have herror := metricApproximationAccuracy_le_one htau1
  let Bq := heightQuotientJetBound G Z d c
  have hBq : 0 ≤ Bq := heightQuotientJetBound_nonneg hG hZ hd hc
  have hpartial (p : Coord) (hp : p ∈ modelSquare) (i : Fin 2) :
      |coordPartial i (hessianQuotient gTau z) p| ≤ Bq :=
    hf.quotientBound [i] (by norm_num) p hp
  have hlocal : FiniteCapMetricJets gTau Y J (lowerCapPointwiseRequests n R) := by
    intro b hb i j k hk p hp
    have hkM : k ≤ m := lowerCapPointwiseRequests_full_order_le n R b hb hk
    have hpS := hf.image_subset_square b.2 hp
    have heq : testMetric gStar q0 (L*r/16) N delta (tau : ℝ) =ᶠ[𝓝 p] gStar :=
      testMetric_eventuallyEq_on_lower_cap hf.quotientSmooth hf.domainOpen hf.squareSubset
        hf.continuous hf.range hf.start hf.ode hh.quotient hBq hL hr hpartial hq0 hcenter
        (by linarith : L*r < 2) (by positivity : 0 < L*r/16)
        (by nlinarith [mul_pos hL hr] : L*r/16 ≤ L*r) hrsmall hdelta htau0 hwidth.2
        gStar N b.2 hp
    have hhjet := metric_jet_norm_le_of_approximation_locality hgStar hgTau hV hU
      (hSV hpS) (hf.domainSubset (hf.squareSubset hpS)) heq i j k
      (hbase i j k hkM p hpS) (happrox i j k (hkM.trans hm) p hpS)
    exact hhjet.trans (add_le_add le_rfl herror)
  have hbound := hheight gTau U z Y W hgTau hU (hf.squareSubset.trans hf.domainSubset)
    hg4 hdet hh hf hlocal
  exact hbound ds hds _ (actual_lower_cut_in_cap_image hh hf hG hZ hd hc hL hr hrhalf hLr
    hq0 hcenter hrsmall hx)

theorem exists_actual_finite_sheared_lower_cut_bound_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L r : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L))
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop,
        ∀ (gTau : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
          SmoothPositiveOn gTau U → IsOpen U →
          (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) →
          CapInductionHeight gTau U Z c e0 z →
          CapInductionFlow gTau U G Z d c e0 kappa z Y W →
          |hessianQuotient gTau z 0-q0| ≤ 1/(100*L) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
              testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          ∀ ds : List (Fin 2), ds.length ≤ n → ∀ x : ℝ, |x| ≤ L*r →
            |iteratedCoordPartial ds (heightInShearCoordinates z q0) (coordinatePoint x (-r))| ≤ C := by
  obtain ⟨C,hC,hcut⟩ := exists_actual_finite_lower_cut_bound_at_radius
    (e0 := e0) (kappa := kappa) hgStar hV hSV hG hZ hd hc hL hq0 hr hrhalf hLr hrsmall n
  refine ⟨(2*(1+|q0|))^n*C,by positivity,?_⟩
  intro N delta hdelt
  filter_upwards [hcut N delta hdelt] with tau hcutTau
  intro gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happ ds hds x hx
  let S : Set Coord := {p | ∃ t : ℝ, |t| ≤ L*r ∧ p = inverseShearCoordinates q0 (boxPoint t (-r))}
  have hSU : S ⊆ U := by
    rintro p ⟨t,ht,rfl⟩
    exact hf.domainSubset (hf.squareSubset (inverseShear_lower_cut_mem_modelSquare hr hrhalf hLr hq0 ht))
  have hbound : CoordinateBound z S n C := by
    intro es hes p hp
    obtain ⟨t,ht,rfl⟩ := hp
    exact hcutTau gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happ es hes t ht
  exact SmoothLocal.Pulse.CoordinateBound.inverse_shear hbound hh.smooth hU hSU hC q0 ds hds
    (coordinatePoint x (-r)) ⟨x,hx,rfl⟩

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_FixedRadiusOffPulseCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix NNReal

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_off_pulse_cauchy_bounds_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
        ∀ᶠ tau : ℕ in atTop,
          ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
            (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
            SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
            CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
            CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
            (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
              ‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B := by
  let L := boundedClassWidth kappa M
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  obtain ⟨A0,hA0,hcutK⟩ := exists_actual_finite_sheared_lower_cut_bound_at_radius
    (G := G) (Z := (M : ℝ)) (d := d) (c := 1/(M : ℝ)) (e0 := 1/(M : ℝ))
    (kappa := kappa) (q0 := q0) (L := L) hgStar hV hSV hG (Nat.cast_nonneg M) hd
      (one_div_pos.mpr hMR) hL hq0 hr hrhalf hLr hrsmall (max 8 (K+2))
  let A : ℝ≥0 := ⟨A0,hA0⟩
  obtain ⟨Cmetric,hCmetric,hmetricK⟩ := exists_uniform_off_pulse_sheared_metric_bounds
    hgStar hV hSV hL hr hrhalf hLr hq0 (max 9 (K+3))
  obtain ⟨B,hB,hcauchy⟩ := exists_bounded_patch_cauchy_bound G d kappa q0 r Cmetric M A
    hG hd hkappa hM hr hrhalf hCmetric hq0 hLr hrsmall K
  refine ⟨B,hB,?_⟩
  intro N delta hdelt
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hcutK N delta hdelt,hwidth,
    eventually_ge_atTop (max 1 (max 9 (K+3)))] with tau hcutTau hwidthTau htau
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ x hx n hn
  have htau1 : 1 ≤ tau := (le_max_left _ _).trans htau
  have htauk : max 9 (K+3) ≤ tau := (le_max_right _ _).trans htau
  have htr : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast htau1)
  have hdw : delta/(tau : ℝ) ≤ r := by
    have he : delta/(tau : ℝ) = 2*(delta/(2*(tau : ℝ))) := by ring
    rw [he]
    linarith [hwidthTau.2]
  have hb0 : -delta/(tau : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hdelt.le) htr.le
  have hab : -r ≤ -delta/(tau : ℝ) := by simpa only [neg_div] using neg_le_neg hdw
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hfullMetric := hmetricK N delta hdelt tau htau1 htauk
    (perturbedMetric g0 eta.val) U hg hU hSU happ
  have hmetric : ∀ i j, CoordinateBound
      (fun p => metricInShearCoordinates (perturbedMetric g0 eta.val) q0 p i j)
      (shrinkingSlab (-(L*r)) (L*r) (-r) (-delta/(tau : ℝ)) (L/4)) (max 9 (K+3)) Cmetric := by
    intro i j ds hds p hp
    have haxes := shrinking_class_slab_axis_bounds hr.le hb0 hp
    exact hfullMetric i j ds hds p ⟨haxes.1,hp.1⟩
  have hactualCut : ∀ ds : List (Fin 2), ds.length ≤ max 8 (K+2) →
      ∀ x : ℝ, |x| ≤ L*r →
        |iteratedCoordPartial ds (heightInShearCoordinates z q0) (coordinatePoint x (-r))| ≤ (A : ℝ) :=
    hcutTau (perturbedMetric g0 eta.val) U W z Y hg hU hgB hdet hh hf hcenter happ
  exact hcauchy g0 eta z (-delta/(tau : ℝ)) hclass hab hb0 hgB hdet hcenter hmetric hactualCut x hx n hn

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QMetricFirstErrorBound
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_actual_Q_forcing_error_bound (B D A : ℝ) {d c : ℝ}
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hd : 0 < d) (hc : 0 < c) :
    ∃ H C : ℝ, 0 ≤ H ∧ 0 ≤ C ∧
      ∀ (gTau gStar : MetricField) (U : Set Coord),
        SmoothPositiveOn gTau U → SmoothPositiveOn gStar U → IsOpen U →
        ∀ (z : Coord → ℝ) (p : Coord), p ∈ U → ∀ epsilon leading : ℝ,
          ‖qFirstBundle gStar (qSolutionJet z p)‖ ≤ B → d ≤ (gStar p).det →
          c ≤ |covHessian gStar z p 0 0| →
          ‖actualCurvatureFirstInput gTau p-actualCurvatureFirstInput gStar p‖ ≤ epsilon →
          epsilon ≤ 1 → (4*max B 0+2)*epsilon ≤ d/2 → H*epsilon ≤ c/2 →
          |curvatureDensity gTau p| ≤ D → |forcingCoefficient gStar z p| ≤ A →
          |(sixVariableQ gTau (qSolutionJet z p)-sixVariableQ gStar (qSolutionJet z p))-
              2*forcingCoefficient gStar z p*leading| ≤
            2*A*|(curvatureDensity gTau p-curvatureDensity gStar p)-leading|+C*epsilon := by
  obtain ⟨H,C,hH,hC,herror⟩ := exists_uniform_qMetricFirstError_bound B D hD hd hc
  refine ⟨H,C,hH,hC,?_⟩
  intro gTau gStar U hgTau hgStar hU z p hp epsilon leading hB hdet hxx hdist
    he1 hsmall hxxsmall hdensity hforce
  obtain ⟨hfloor,herr⟩ := herror gTau gStar (qSolutionJet z p) epsilon hB
    (by simpa only [statePoint_qSolutionJet] using hdet)
    (by simpa only [stateQDenominator_qSolutionJet] using hxx)
    (by simpa only [statePoint_qSolutionJet] using hdist) he1 hsmall hxxsmall
    (by simpa only [statePoint_qSolutionJet] using hdensity)
  have hxxStar : covHessian gStar z p 0 0 ≠ 0 := by
    intro hz
    rw [hz,abs_zero] at hxx
    linarith
  have hxxTau : covHessian gTau z p 0 0 ≠ 0 := by
    rw [stateQDenominator_qSolutionJet] at hfloor
    intro hz
    rw [hz,abs_zero] at hfloor
    linarith
  rw [actual_Q_metric_forcing_leading_identity hgTau hgStar hU z hp hxxTau hxxStar]
  have hfactor : |2*forcingCoefficient gStar z p| ≤ 2*A := by
    simpa only [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      mul_le_mul_of_nonneg_left hforce (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ |2*forcingCoefficient gStar z p| *
        |(curvatureDensity gTau p-curvatureDensity gStar p)-leading|+
        |qMetricFirstError gTau gStar (qSolutionJet z p)| := by
      simpa only [abs_mul] using abs_add_le
        (2*forcingCoefficient gStar z p*((curvatureDensity gTau p-curvatureDensity gStar p)-leading))
        (qMetricFirstError gTau gStar (qSolutionJet z p))
    _ ≤ _ := add_le_add
      (mul_le_mul hfactor le_rfl (abs_nonneg _) (mul_nonneg (by norm_num) hA)) herr

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ReferencePulseEdgeInitial
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Perturbation
open SmoothLocal.Flow SmoothLocal.Taylor

theorem exists_bounded_patch_reference_initial_floor
    (G kappa d q0 : ℝ) (M : ℕ) (hG : 0 ≤ G)
    (hkappa : 0 < kappa) (hd : 0 < d) (hM : 0 < M) (hq0 : |q0| ≤ 1 / 20) :
    ∃ tau0 : ℕ, 1 ≤ tau0 ∧
      ∀ (g0 gStar : MetricField) (V : Set Coord) (eta : metricPatchSet g0 kappa)
        (z : Coord → ℝ) (r : ℝ) (N : ℕ) (delta : ℝ) (tau : ℕ),
      SmoothPositiveOn gStar V → IsOpen V → SmoothLocal.Flow.modelSquare ⊆ V →
      BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
      0 < r → boundedClassWidth kappa M * r ≤ 1 / 20 →
      heightQuotientJetBound G (M : ℝ) d (1 / (M : ℝ)) *
        (r + 107 * (boundedClassWidth kappa M * r) / 100) ≤
          9 / (100 * boundedClassWidth kappa M) →
      (∀ i j k, k ≤ 4 → ∀ p ∈ SmoothLocal.Flow.modelSquare,
        ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
      (∀ p ∈ SmoothLocal.Flow.modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
      |hessianQuotient (perturbedMetric g0 eta.val) z 0 - q0| ≤
        1 / (100 * boundedClassWidth kappa M) →
      0 < delta → tau0 ≤ tau → delta / (tau : ℝ) ≤ r →
      (∀ i j k, k ≤ tau → ∀ p ∈ SmoothLocal.Flow.modelSquare,
        ‖iteratedFDeriv ℝ k
          (fun a => perturbedMetric g0 eta.val a i j -
            testMetric gStar q0 (boundedClassWidth kappa M * r / 16) N delta (tau : ℝ) a i j) p‖ ≤
              metricApproximationAccuracy tau) →
      ∀ x ∈ Ioo (-(boundedClassWidth kappa M * r)) (boundedClassWidth kappa M * r),
      (boundedClassSpeed kappa M)^2 / (4 * (M : ℝ)) ≤
        |covHessian (metricInShearCoordinates gStar q0)
          (linearCauchy (-delta / (tau : ℝ))
            (heightCauchyValue (heightInShearCoordinates z q0) (-delta / (tau : ℝ)))
            (heightCauchyVelocity (heightInShearCoordinates z q0) (-delta / (tau : ℝ))))
          ![x, -delta / (tau : ℝ)] 0 0| := by
  let c := (boundedClassSpeed kappa M)^2 / (2 * (M : ℝ))
  have hc : 0 < c := boundedClassShearHxxFloor_pos hkappa hM
  obtain ⟨epsilon, he, htol⟩ := exists_reference_linearCauchy_XX_tolerance
    (8 * G) (boundedClassShearedStateBudget q0 M) hd hc
  obtain ⟨tau0, htau0, herror⟩ := exists_first_error_threshold he
  refine ⟨tau0, htau0, ?_⟩
  intro g0 gStar V eta z r N delta tau hgStar hV hSV hclass hr hLr hrsmall
    hgB hdet hcenter hdelta htau hwidth happrox x hx
  let g := perturbedMetric g0 eta.val
  let L := boundedClassWidth kappa M
  let a := -delta / (tau : ℝ)
  have hclass0 := hclass
  obtain ⟨_, hadm, _, _, _⟩ := hclass
  obtain ⟨U, hU, hSU, hg, hz, _, _, _, _⟩ := hadm
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hL1 : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M)
  have hrsmall' : r ≤ 1 / 20 := by
    have hh : r ≤ L * r := by nlinarith
    exact hh.trans hLr
  have htauN : 1 ≤ tau := htau0.trans htau
  have htauR : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le (by exact_mod_cast htauN)
  have habs : |a| ≤ r := by
    dsimp [a]
    rw [abs_div, abs_neg, abs_of_pos hdelta, abs_of_pos htauR]
    exact hwidth
  have hcutCentral (y : ℝ) (hy : y ∈ Ioo (-(L * r)) (L * r)) :
      inverseShearCoordinates q0 ![y, a] ∈ centralBox :=
    inverseShear_slab_mem_centralBox hL1 hr.le hLr hq0 (abs_le.mpr ⟨hy.1.le, hy.2.le⟩) habs
  have hcutS (y : ℝ) (hy : y ∈ Ioo (-(L * r)) (L * r)) :
      inverseShearCoordinates q0 ![y, a] ∈ SmoothLocal.Flow.modelSquare :=
    centralBox_subset_modelSquare (hcutCentral y hy)
  have hpS := hcutS x hx
  have hpU := hSU hpS
  have hpx : |x| ≤ L * r := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  have hsmall := bounded_class_slab_quotient_small_of_cap_radius hclass0 hG hd hr.le hq0 hrsmall
    hgB hdet hcenter hpS hpx habs
  have hK : gaussianCurvature g (inverseShearCoordinates q0 ![x, a]) ≤ -kappa / 2 :=
    (eta.property.2 _ (hcutCentral x hx)).le
  obtain ⟨_, hxx, _, _⟩ := bounded_class_shear_estimates hclass0 hkappa hpS hK hsmall
  have hq1 : |q0| ≤ 1 := hq0.trans (by norm_num)
  have hfirst := sheared_first_input_norm_le_of_original_jets hg hU hpU hG hq1
    (fun i j k hk => hgB i j k (by omega) _ hpS)
  have hstate := bounded_class_sheared_solution_state_bound hclass0 q0 hpS
    (show |(![x,a] : Coord) 0| ≤ 1 ∧ |(![x,a] : Coord) 1| ≤ 1 from
      ⟨by change |x| ≤ 1; exact hpx.trans (hLr.trans (by norm_num)),
        by change |a| ≤ 1; exact habs.trans (hrsmall'.trans (by norm_num))⟩)
  have hdet0 : d ≤ (g (inverseShearCoordinates q0 ![x,a])).det := by
    have hh := hdet _ hpS
    rw [abs_of_pos (hg.2 _ hpU).det_pos] at hh
    exact hh
  have hdetS : d ≤ (metricInShearCoordinates g q0 ![x,a]).det := by
    rw [metricDet_in_shear_coordinates]
    exact hdet0
  have hdist := actual_pulse_edge_reference_first_distance hg hgStar hU hV hq1
    (div_pos (mul_pos hL hr) (by norm_num)) hdelta htauN hpU (hSV hpS)
    (fun i j k hk => happrox i j k hk _ hpS)
  have hUS := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hzS := heightInShearCoordinates_contDiffOn hz q0
  have hresult := htol (metricInShearCoordinates g q0) (metricInShearCoordinates gStar q0)
    (heightInShearCoordinates z q0) (inverseShearCoordinates q0 ⁻¹' U) hzS hUS
    (-(L * r)) (L * r) a (fun y hy => hSU (hcutS y hy)) x hx hfirst hstate hdetS hxx
    (hdist.trans (herror tau htau))
  have heq : c / 2 = (boundedClassSpeed kappa M)^2 / (4 * (M : ℝ)) := by
    dsimp [c]
    ring
  rw [heq] at hresult
  exact hresult

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorQJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem qCompactTube_finite_Q_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ N, ∀ w ∈ qCompactTube g S M c,
      ‖iteratedFDeriv ℝ n (sixVariableQ g) w‖ ≤ C := by
  classical
  have hh : ∀ j : Fin (N + 1), ∃ C : ℝ, ∀ w ∈ qCompactTube g S M c,
      ‖iteratedFDeriv ℝ j.val (sixVariableQ g) w‖ ≤ C :=
    fun j => qCompactTube_derivative_bound hg hU hS hSU M hc
      (sixVariableQ_contDiffOn hg hU) j.val
  choose A hA using hh
  refine ⟨∑ j : Fin (N + 1), |A j|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro n hn w hw
  let j : Fin (N + 1) := ⟨n, by omega⟩
  exact (hA j w hw).trans ((le_abs_self (A j)).trans
    (Finset.single_le_sum (fun index _ => abs_nonneg (A index)) (Finset.mem_univ j)))

theorem Q_height_composition_fullJet_bound {g : MetricField} {U S : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    {p : Coord} (hpI : p ∈ spatialStrip I) (hpS : p ∈ S) (hSU : S ⊆ U)
    {M c B C : ℝ} (hM : 0 ≤ M) (hc : 0 < c) (hstate : ‖qSolutionJet P p‖ ≤ M)
    (hden : c ≤ |covHessian g P p 0 0|) (n : ℕ)
    (hB : ∀ j ≤ n + 2, ‖iteratedFDeriv ℝ j P p‖ ≤ B)
    (hC : ∀ j ≤ n, ∀ w ∈ qCompactTube g S M c,
      ‖iteratedFDeriv ℝ j (sixVariableQ g) w‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun q => sixVariableQ g (qSolutionJet P q)) p‖ ≤
      (n.factorial : ℝ) * C * (max 1 B)^n := by
  have hxx : covHessian g P p 0 0 ≠ 0 := by
    intro h
    rw [h, abs_zero] at hden
    linarith
  have hpD := mem_comparisonDomain hpI (hSU hpS) hxx
  have hD := comparisonDomain_isOpen hg hU hI hP
  have hQ := sixVariableQ_contDiffOn hg hU
  have hQD := darbouxQStateDomain_isOpen hg hU
  have hinput := (qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).mono
    (show comparisonDomain g U P I ⊆ spatialStrip I from inter_subset_left)
  have hmap : MapsTo (qSolutionJet P) (comparisonDomain g U P I) (darbouxQStateDomain g U) :=
    fun _ hq => hq.2
  have houter : ∀ j, j ≤ n →
      ‖iteratedFDerivWithin ℝ j (sixVariableQ g) (darbouxQStateDomain g U) (qSolutionJet P p)‖ ≤ C := by
    intro j hj
    rw [iteratedFDerivWithin_of_isOpen j hQD (hmap hpD)]
    exact hC j hj _ (qSolutionJet_mem_qCompactTube hpS hM hstate hden)
  have hinner : ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDerivWithin ℝ j (qSolutionJet P) (comparisonDomain g U P I) p‖ ≤ (max 1 B)^j := by
    intro j hj hjn
    rw [iteratedFDerivWithin_of_isOpen j hD hpD]
    exact (qSolutionJet_positive_fullJet_bound hP (spatialStrip_isOpen hI) hpI hj
      (fun k hk => hB k (by omega))).trans (le_self_pow₀ (le_max_left _ _) (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le hQ hinput
    (WithTop.coe_le_coe.mpr le_top) hQD.uniqueDiffOn hD.uniqueDiffOn hmap hpD houter hinner
  rw [iteratedFDerivWithin_of_isOpen n hD hpD] at hcomp
  exact hcomp

theorem exists_uniform_qResidual_fullJet_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Coord → ℝ) (I : Set ℝ), IsOpen I →
      ContDiffOn ℝ ∞ P (spatialStrip I) → ∀ p : Coord, p ∈ spatialStrip I → p ∈ S →
      ‖qSolutionJet P p‖ ≤ M → c ≤ |covHessian g P p 0 0| →
      ∀ (n : ℕ), n ≤ N → ∀ B : ℝ,
      (∀ j ≤ n + 2, ‖iteratedFDeriv ℝ j P p‖ ≤ B) →
      ‖iteratedFDeriv ℝ n (qResidual g P) p‖ ≤
        B + (n.factorial : ℝ) * C * (max 1 B)^n := by
  obtain ⟨C, hC, hCQ⟩ := qCompactTube_finite_Q_bound hg hU hS hSU M hc N
  refine ⟨C, hC, ?_⟩
  intro P I hI hP p hpI hpS hstate hden n hn B hB
  have hxx : covHessian g P p 0 0 ≠ 0 := by
    intro h
    rw [h, abs_zero] at hden
    linarith
  have htt := (partial_contDiffOn (partial_contDiffOn hP (spatialStrip_isOpen hI) 1)
    (spatialStrip_isOpen hI) 1).contDiffAt ((spatialStrip_isOpen hI).mem_nhds hpI)
  have hQc := (sixVariableQ_contDiffAt_solutionJet hg hU (hSU hpS) hxx).comp p
    ((qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).contDiffAt
      ((spatialStrip_isOpen hI).mem_nhds hpI))
  have hsecond : ‖iteratedFDeriv ℝ n (coordPartial 1 (coordPartial 1 P)) p‖ ≤ B :=
    ((norm_iteratedFDeriv_coordPartial_le (partial_contDiffOn hP (spatialStrip_isOpen hI) 1)
      (spatialStrip_isOpen hI) hpI 1 n).trans
        (norm_iteratedFDeriv_coordPartial_le hP (spatialStrip_isOpen hI) hpI 1 (n + 1))).trans
          (hB (n + 1 + 1) (by omega))
  have hQbound := Q_height_composition_fullJet_bound hg hU hI hP hpI hpS hSU hM hc
    hstate hden n hB (fun j hj => hCQ j (hj.trans hn))
  change ‖iteratedFDeriv ℝ n (coordPartial 1 (coordPartial 1 P) -
    (sixVariableQ g ∘ qSolutionJet P)) p‖ ≤ _
  rw [iteratedFDeriv_sub_apply (htt.of_le (WithTop.coe_le_coe.mpr le_top))
    (hQc.of_le (WithTop.coe_le_coe.mpr le_top))]
  exact (norm_sub_le _ _).trans (add_le_add hsecond hQbound)

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem nextTaylorCoefficient_fullJet_le {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (a x : ℝ) (hx : x ∈ I) (hpU : (![x, a] : Coord) ∈ U)
    (hxx : covHessian g P ![x, a] 0 0 ≠ 0) (n k : ℕ) :
    ‖iteratedFDeriv ℝ k (nextTaylorCoefficient g a P n) x‖ ≤
      ‖iteratedFDeriv ℝ (k + n) (qResidual g P) ![x, a]‖ := by
  have hD := comparisonDomain_isOpen hg hU hI hP
  have hR := qResidual_contDiffOn hg hU hI hP
  have hp := mem_comparisonDomain hx hpU hxx
  change ‖iteratedFDeriv ℝ k (-(fun y => verticalJet (qResidual g P) n ![y, a])) x‖ ≤ _
  rw [iteratedFDeriv_neg_apply, norm_neg]
  exact (norm_initial_slice_jet_le (verticalJet_contDiffOn hD hR n) hD a x hp k).trans
    (norm_verticalJet_fullJet_le hR hD hp n k)

theorem exists_uniform_nextTaylorCoefficient_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Coord → ℝ) (I : Set ℝ), IsOpen I →
      ContDiffOn ℝ ∞ P (spatialStrip I) → ∀ a x : ℝ, x ∈ I → (![x, a] : Coord) ∈ S →
      ‖qSolutionJet P ![x, a]‖ ≤ M → c ≤ |covHessian g P ![x, a] 0 0| →
      ∀ n k : ℕ, k + n ≤ N → ∀ B : ℝ,
      (∀ j ≤ k + n + 2, ‖iteratedFDeriv ℝ j P ![x, a]‖ ≤ B) →
      ‖iteratedFDeriv ℝ k (nextTaylorCoefficient g a P n) x‖ ≤
        B + ((k + n).factorial : ℝ) * C * (max 1 B)^(k + n) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_qResidual_fullJet_bound hg hU hS hSU M hM hc N
  refine ⟨C, hC, ?_⟩
  intro P I hI hP a x hx hpS hstate hden n k hkn B hB
  have hxx : covHessian g P ![x, a] 0 0 ≠ 0 := by
    intro h
    rw [h, abs_zero] at hden
    linarith
  exact (nextTaylorCoefficient_fullJet_le hg hU hI hP a x hx (hSU hpS) hxx n k).trans
    (hbound P I hI hP ![x, a] hx hpS hstate hden (k + n) hkn B hB)

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_UniformTaylorPolynomial
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem uniform_taylorApproximation_jets
    {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (B : ℝ) (hB : 0 ≤ B) :
    ∀ N k : ℕ, ∃ R : ℝ, 0 ≤ R ∧
      ∀ (u0 u1 : ℝ → ℝ) (I J : Set ℝ) (a : ℝ), IsOpen I → J ⊆ I →
      ContDiffOn ℝ ∞ u0 I → ContDiffOn ℝ ∞ u1 I →
      (∀ x ∈ I, (![x, a] : Coord) ∈ S) →
      (∀ x ∈ I, ‖qSolutionJet (linearCauchy a u0 u1) ![x, a]‖ ≤ M) →
      (∀ x ∈ I, c ≤ |covHessian g (linearCauchy a u0 u1) ![x, a] 0 0|) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N k, ‖iteratedFDeriv ℝ j u0 x‖ ≤ B) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N k, ‖iteratedFDeriv ℝ j u1 x‖ ≤ B) →
      ∀ j ≤ k, ∀ p : Coord, p 0 ∈ J → |p 1 - a| ≤ 1 →
        ‖iteratedFDeriv ℝ j (taylorApproximation g a u0 u1 N) p‖ ≤ R := by
  classical
  intro N
  induction N with
  | zero =>
    intro k
    refine ⟨(1 + (2 : ℝ)^k) * B, mul_nonneg (by positivity) hB, ?_⟩
    intro u0 u1 I J a hI hJI h0 h1 _ _ _ h0B h1B j hj p hp ht
    have hpb := linearCauchy_fullJet_bound h0 h1 hI a j (hJI hp) ht hB
      (fun i hi => h0B (p 0) hp i (by simpa only [taylorInitialRequest, zero_mul, Nat.add_zero] using hi.trans hj))
      (fun i hi => h1B (p 0) hp i (by simpa only [taylorInitialRequest, zero_mul, Nat.add_zero] using hi.trans hj))
    exact hpb.trans (mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)) hB)
  | succ n ih =>
    intro k
    obtain ⟨R0, hR0, hprevious⟩ := ih (k + n + 2)
    obtain ⟨C, hC, hcoefficient⟩ := exists_uniform_nextTaylorCoefficient_bound
      hg hU hS hSU M hM hc (k + n)
    let RC : ℝ := ∑ i : Fin (k + 1),
      (R0 + ((i.val + n).factorial : ℝ) * C * (max 1 R0)^(i.val + n))
    have hRC : 0 ≤ RC := Finset.sum_nonneg (fun i _ => by positivity)
    refine ⟨R0 + (2 : ℝ)^k * RC, add_nonneg hR0 (mul_nonneg (by positivity) hRC), ?_⟩
    intro u0 u1 I J a hI hJI h0 h1 hcut hstate hden h0B h1B j hj p hp ht
    have hcutU : ∀ x ∈ I, (![x, a] : Coord) ∈ U := fun x hx => hSU (hcut x hx)
    have hxx : ∀ x ∈ I, covHessian g (linearCauchy a u0 u1) ![x, a] 0 0 ≠ 0 := by
      intro x hx hh
      have hd := hden x hx
      rw [hh, abs_zero] at hd
      linarith
    obtain ⟨hP, hjet, _⟩ := taylorApproximation_properties hg hU hI h0 h1 a hcutU hxx n
    have hstateN : ∀ x ∈ I, ‖qSolutionJet (taylorApproximation g a u0 u1 n) ![x, a]‖ ≤ M := by
      intro x hx
      rw [hjet x hx]
      exact hstate x hx
    have hdenN : ∀ x ∈ I,
        c ≤ |covHessian g (taylorApproximation g a u0 u1 n) ![x, a] 0 0| := by
      intro x hx
      rw [← stateQDenominator_qSolutionJet, hjet x hx, stateQDenominator_qSolutionJet]
      exact hden x hx
    have hxxN : ∀ x ∈ I,
        covHessian g (taylorApproximation g a u0 u1 n) ![x, a] 0 0 ≠ 0 := by
      intro x hx hh
      have hd := hdenN x hx
      rw [hh, abs_zero] at hd
      linarith
    have hprev := hprevious u0 u1 I J a hI hJI h0 h1 hcut hstate hden
      (fun x hx i hi => h0B x hx i (hi.trans (taylorInitialRequest_step n k)))
      (fun x hx i hi => h1B x hx i (hi.trans (taylorInitialRequest_step n k)))
    have hCoeff : ContDiffOn ℝ ∞
        (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) I :=
      nextTaylorCoefficient_contDiffOn hg hU hI hP a n hcutU hxxN
    have hCoeffB : ∀ x ∈ J, ∀ i ≤ k,
        ‖iteratedFDeriv ℝ i (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) x‖ ≤ RC := by
      intro x hx i hi
      have hb := hcoefficient (taylorApproximation g a u0 u1 n) I hI hP a x (hJI hx)
        (hcut x (hJI hx)) (hstateN x (hJI hx)) (hdenN x (hJI hx)) n i (by omega) R0
        (fun l hl => hprev l (by omega) ![x, a] hx (by simp))
      let fi : Fin (k + 1) := ⟨i, by omega⟩
      have hsingle : R0 + ((fi.val + n).factorial : ℝ) * C * (max 1 R0)^(fi.val + n) ≤ RC :=
        Finset.single_le_sum
          (f := fun l : Fin (k + 1) => R0 + ((l.val + n).factorial : ℝ) * C * (max 1 R0)^(l.val + n))
          (fun l _ => by positivity) (Finset.mem_univ fi)
      exact hb.trans hsingle
    have hcorr := separatedTimePower_fullJet_bound hCoeff hI a (n + 2) j (hJI hp) ht hRC
      (fun i hi => hCoeffB (p 0) hp i (hi.trans hj))
    have hprevp := hprev j (by omega) p hp ht
    have hcorrsmooth := taylorCorrection_contDiffOn hCoeff a n
    change ‖iteratedFDeriv ℝ j
      (taylorApproximation g a u0 u1 n +
        taylorCorrection (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) a n) p‖ ≤ _
    rw [iteratedFDeriv_add_apply
      ((hP.contDiffAt ((spatialStrip_isOpen hI).mem_nhds (hJI hp))).of_le (WithTop.coe_le_coe.mpr le_top))
      ((hcorrsmooth.contDiffAt ((spatialStrip_isOpen hI).mem_nhds (hJI hp))).of_le
        (WithTop.coe_le_coe.mpr le_top))]
    exact (norm_add_le _ _).trans (add_le_add hprevp (hcorr.trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hRC)))

end SmoothLocal.Taylor

end

end OAI
end


