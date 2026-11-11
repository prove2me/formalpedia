-- Prove2me | Definitions.Def_Q226II010
-- name    : Q226II010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:42:30.920205+00:00
-- url     : https://prove2.me/theorems/8d902909-a183-4981-a875-ed369aadee7b
-- title:
--   Definitions bundle Q226II010 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 48 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Assembly_SupportedPerturbations`, `IsometricImmersion_Caps_CauchyReflection`, `IsometricImmersion_Caps_PulseReflection`, `IsometricImmersion_Comparison_ComparisonGradientSlice`, `IsometricImmersion_Comparison_CurvatureComparisonControl`, `IsometricImmersion_Darboux_QActualSegmentTransfer`, `IsometricImmersion_Estimates_MovingSourceBounds`, `IsometricImmersion_Pulses_ActualForcingMoment`, `IsometricImmersion_Pulses_ActualTwoSidedPulseSeparation`, `IsometricImmersion_Pulses_PulseMomentError`, `IsometricImmersion_Pulses_PulseMomentGeometry`, `IsometricImmersion_Pulses_ShearedPulseRegions`, `IsometricImmersion_Taylor_UniformTaylorDenominator`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II003`, `Q226II004`, `Q226II005` and `Q226II006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q226II013`.
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
import Mathlib.Analysis.Convex.Topology
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
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.Count
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
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
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_IsometricImmersion
import Definitions.Def_Q226II003
import Definitions.Def_Q226II004
import Definitions.Def_Q226II005
import Definitions.Def_Q226II006

section
-- module Solutions.Q226_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
end OAICompat434

end OAI
end

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

theorem supportedTensor_eval_continuous (p : Coord) (i j : Fin 2) :
    Continuous (fun η : SupportedTensor => η p i j) := by
  have hjet : Continuous (fun η : SupportedTensor =>
      ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ 0 η p) :=
    (continuous_eval_const p).comp (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ 0).continuous
  have hval : Continuous (fun η : SupportedTensor => η p) := by
    have h := (continuousMultilinearCurryFin0 ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ)).continuous.comp hjet
    simp only [Function.comp_def, ContDiffMapSupportedIn.structureMapCLM_zero_apply,
      continuousMultilinearCurryFin0_apply, ContinuousMultilinearMap.uncurry0_apply] at h
    exact h
  exact (continuous_apply j).comp ((continuous_apply i).comp hval)

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_PulseReflection
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem inverseShear_reflect (q0 : ℝ) (p : Coord) :
    inverseShearCoordinates q0 (reflectPoint p) =
      reflectPoint (inverseShearCoordinates (-q0) p) := by
  ext i
  fin_cases i
  · change p 0 = p 0
    rfl
  · change -p 1-q0*p 0 = -(p 1-(-q0)*p 0)
    ring

theorem shear_reflect (q0 : ℝ) (p : Coord) :
    shearCoordinates q0 (reflectPoint p) =
      reflectPoint (shearCoordinates (-q0) p) := by
  ext i
  fin_cases i
  · change p 0 = p 0
    rfl
  · change -p 1+q0*p 0 = -(p 1+(-q0)*p 0)
    ring

theorem pulseScalar_reflect (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    pulseScalar a N delta tau (reflectPoint p) = pulseScalar a N delta tau p := by
  simp only [pulseScalar, reflectPoint_zero, reflectPoint_one, mul_neg, neg_div,
    temporalCutoff, axisBump_even]

theorem reflectedMetric_pulseTensor (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) :
    reflectedMetric (pulseTensor q0 a N delta tau) = pulseTensor (-q0) a N delta tau := by
  funext p
  ext i j
  rw [reflectedMetric_entry]
  simp only [pulseTensor, shear_reflect, pulseScalar_reflect]
  fin_cases i <;> fin_cases j <;> simp [thetaCovector]

theorem reflectedMetric_testMetric (g : MetricField) (q0 a : ℝ) (N : ℕ)
    (delta tau : ℝ) :
    reflectedMetric (testMetric g q0 a N delta tau) =
      testMetric (reflectedMetric g) (-q0) a N delta tau := by
  rw [testMetric, reflectedMetric_add, reflectedMetric_pulseTensor]
  rfl

theorem height_shear_reflection (z : Coord → ℝ) (q0 : ℝ) :
    heightInShearCoordinates (reflectedScalar z) (-q0) =
      reflectedScalar (heightInShearCoordinates z q0) := by
  funext p
  change z (reflectPoint (inverseShearCoordinates (-q0) p)) =
    z (inverseShearCoordinates q0 (reflectPoint p))
  rw [inverseShear_reflect]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QActualSegmentTransfer
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem qSolutionJet_norm_bound {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    {R Z : ℝ} (hR : 0 ≤ R) (_hZ : 0 ≤ Z) (hpB : ‖p‖ ≤ R)
    (hzB : ∀ k ≤ 2, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) :
    ‖qSolutionJet z p‖ ≤ max R Z := by
  have hw (ds : List (Fin 2)) (hds : ds.length ≤ 2) :
      |iteratedCoordPartial ds z p| ≤ Z :=
    (norm_iteratedCoordPartial_le_jet hz hU ds hp).trans (hzB ds.length hds)
  have hcoord (i : Fin 2) : |p i| ≤ R := (norm_le_pi_norm p i).trans hpB
  apply (pi_norm_le_iff_of_nonneg (hR.trans (le_max_left _ _))).mpr
  intro i
  fin_cases i
  · exact (hcoord 0).trans (le_max_left _ _)
  · exact (hcoord 1).trans (le_max_left _ _)
  · exact (hw [0] (by norm_num)).trans (le_max_right _ _)
  · exact (hw [1] (by norm_num)).trans (le_max_right _ _)
  · exact (hw [0, 1] (by norm_num)).trans (le_max_right _ _)
  · exact (hw [0, 0] (by norm_num)).trans (le_max_right _ _)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CauchyReflection
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.Flow.Reflection SmoothLocal.Pulse

theorem reflectPoint_initialPoint (x a : ℝ) :
    reflectPoint (![x,a] : Coord) = ![x,-a] := by
  ext i
  fin_cases i <;> simp

theorem coordPartial_one_reflectedScalar (f : Coord → ℝ) (p : Coord) :
    coordPartial 1 (reflectedScalar f) p = -coordPartial 1 f (reflectPoint p) := by
  have he : fderiv ℝ (f ∘ reflectPoint) p =
      (fderiv ℝ f (reflectPoint p)).comp
        (reflectionIsometry.toContinuousLinearEquiv : Coord →L[ℝ] Coord) :=
    reflectionIsometry.toContinuousLinearEquiv.comp_right_fderiv (f := f) (x := p)
  change fderiv ℝ (f ∘ reflectPoint) p (Pi.single 1 (1 : ℝ)) =
    -fderiv ℝ f (reflectPoint p) (Pi.single 1 (1 : ℝ))
  rw [he, ContinuousLinearMap.comp_apply]
  have hb : reflectionIsometry.toContinuousLinearEquiv (Pi.single 1 (1 : ℝ)) =
      -(Pi.single 1 (1 : ℝ) : Coord) := by
    ext i
    fin_cases i <;> simp [reflectionIsometry,reflectPoint]
  change (fderiv ℝ f (reflectPoint p)) (reflectionIsometry (Pi.single 1 1)) =
    -(fderiv ℝ f (reflectPoint p)) (Pi.single 1 1)
  change reflectionIsometry (Pi.single 1 (1 : ℝ)) = -(Pi.single 1 (1 : ℝ) : Coord) at hb
  rw [hb,map_neg]

theorem heightCauchyValue_reflected (z : Coord → ℝ) (a : ℝ) :
    heightCauchyValue (reflectedScalar z) a = heightCauchyValue z (-a) := by
  funext x
  change z (reflectPoint ![x,a]) = z ![x,-a]
  rw [reflectPoint_initialPoint]

theorem heightCauchyVelocity_reflected (z : Coord → ℝ) (a : ℝ) :
    heightCauchyVelocity (reflectedScalar z) a = -heightCauchyVelocity z (-a) := by
  funext x
  change coordPartial 1 (reflectedScalar z) ![x,a] = -coordPartial 1 z ![x,-a]
  rw [coordPartial_one_reflectedScalar,reflectPoint_initialPoint]

theorem reflected_Cauchy_jet_norms (z : Coord → ℝ) (a x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (heightCauchyValue (reflectedScalar z) a) x‖ =
      ‖iteratedFDeriv ℝ n (heightCauchyValue z (-a)) x‖ ∧
    ‖iteratedFDeriv ℝ n (heightCauchyVelocity (reflectedScalar z) a) x‖ =
      ‖iteratedFDeriv ℝ n (heightCauchyVelocity z (-a)) x‖ := by
  simp [heightCauchyValue_reflected,heightCauchyVelocity_reflected,
    iteratedFDeriv_neg_apply]

theorem sheared_reflected_Cauchy_jet_norms (z : Coord → ℝ) (q0 a x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (heightCauchyValue
      (heightInShearCoordinates (reflectedScalar z) (-q0)) a) x‖ =
        ‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0) (-a)) x‖ ∧
    ‖iteratedFDeriv ℝ n (heightCauchyVelocity
      (heightInShearCoordinates (reflectedScalar z) (-q0)) a) x‖ =
        ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0) (-a)) x‖ := by
  rw [height_shear_reflection]
  exact reflected_Cauchy_jet_norms _ a x n

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_CurvatureComparisonControl
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

theorem first_jet_close_segment_subset_tube (a b : CurvatureFirstInput) {B d : ℝ}
    (ha : ‖a‖ ≤ B) (hdet : d ≤ (Matrix.of a.1).det) (hdist : ‖b-a‖ ≤ 1)
    (hsmall : (4*max B 0+2)*‖b-a‖ ≤ d/2) :
    segment ℝ a b ⊆ curvatureFirstTube (max B 0+1) (d/2) := by
  intro x hx
  have hxa : ‖x-a‖ ≤ ‖b-a‖ := by
    have hball : x ∈ Metric.closedBall a ‖b-a‖ :=
      (convex_closedBall a ‖b-a‖).segment_subset
        (by simp) (Metric.mem_closedBall.mpr (dist_eq_norm b a).le) hx
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hball
  have hxnorm : ‖x‖ ≤ max B 0+1 := by
    calc
      _ = ‖(x-a)+a‖ := by rw [sub_add_cancel]
      _ ≤ ‖x-a‖+‖a‖ := norm_add_le _ _
      _ ≤ 1+max B 0 := add_le_add (hxa.trans hdist) (ha.trans (le_max_left _ _))
      _ = _ := by ring
  have hmatrixD : ‖x.1-a.1‖ ≤ ‖b-a‖ :=
    (show ‖x.1-a.1‖ ≤ ‖x-a‖ from norm_fst_le (x-a)).trans hxa
  have hmatrixA : ‖a.1‖ ≤ max B 0 := (norm_fst_le a).trans (ha.trans (le_max_left _ _))
  have hdetdiff := det_sub_le_small_first_distance (Matrix.of a.1) (Matrix.of x.1) (le_max_right B 0)
    (norm_nonneg _) hdist hmatrixA hmatrixD
  have hxdet : d/2 ≤ (Matrix.of x.1).det := by
    have hneg := neg_abs_le ((Matrix.of x.1).det-(Matrix.of a.1).det)
    linarith [hdetdiff.trans hsmall]
  exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxnorm,hxdet⟩

theorem exists_uniform_curvature_first_comparison (B : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : CurvatureFirstInput,
      ‖a‖ ≤ B → d ≤ (Matrix.of a.1).det → ‖b-a‖ ≤ 1 →
      (4*max B 0+2)*‖b-a‖ ≤ d/2 →
      |curvatureFirstFunction b-curvatureFirstFunction a| ≤ C*‖b-a‖ := by
  obtain ⟨C,hC,hbound⟩ := curvatureFirstTube_fderiv_bound (max B 0+1) (half_pos hd)
  refine ⟨C,hC,?_⟩
  intro a b ha hdet hdist hsmall
  have htube := first_jet_close_segment_subset_tube a b ha hdet hdist hsmall
  have hdiff : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ curvatureFirstFunction x := by
    intro x hx
    exact (curvatureFirstFunction_contDiffOn.contDiffAt (curvatureFirstDomain_isOpen.mem_nhds
      (curvatureFirstTube_subset_domain (max B 0+1) (half_pos hd) (htube hx)))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  simpa only [Real.norm_eq_abs] using
    (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le hdiff
      (fun x hx => hbound x (htube hx)) (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseMomentGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem pulseStrip_zero_mem {a delta tau : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ delta) (ht : 0 < tau) :
    boxPoint 0 0 ∈ pulseStrip a delta tau := by
  apply boxPoint_mem <;> constructor <;> linarith [div_nonneg hd ht.le]

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

theorem actual_leading_weighted_moment_eq (g : MetricField) (z : Coord → ℝ)
    (a delta : ℝ) (N : ℕ) {tau : ℝ} (ht : 0 < tau) :
    pulseWeightedMoment a delta tau
      (fun p => 2*forcingCoefficient g z p*pulsePrincipalLeading a N delta tau p) =
      (tau^2/tau^N)*(∫ q in pulsePairRectangle a delta tau,
        forcingCoefficient g z (pulsePairPoint q)*pulseMomentWeight a delta tau q
          ∂volume.prod volume) := by
  have heq (q : ℝ × ℝ) :
      (2*forcingCoefficient g z (pulsePairPoint q)*
        pulsePrincipalLeading a N delta tau (pulsePairPoint q))*pulseTest a tau q.2 =
      (tau^2/tau^N)*(forcingCoefficient g z (pulsePairPoint q)*pulseMomentWeight a delta tau q) := by
    have h0 : pulsePairPoint q 0 = q.2 := by simp [pulsePairPoint,boxPoint]
    have h1 : pulsePairPoint q 1 = q.1 := by simp [pulsePairPoint,boxPoint]
    unfold pulsePrincipalLeading pulseTest pulseMomentWeight
    rw [h0,h1]
    field_simp [ht.ne']
  unfold pulseWeightedMoment
  simp_rw [heq]
  rw [integral_const_mul]

theorem signed_coefficient_weighted_integral_lower
    {a delta tau sigma d0 : ℝ} {D : Coord → ℝ}
    (hD : ContinuousOn D (pulseStrip a delta tau)) (hsigma : |sigma| = 1)
    (hfloor : ∀ p ∈ pulseStrip a delta tau, d0 ≤ sigma*D p) :
    d0*(∫ q in pulsePairRectangle a delta tau, pulseMomentWeight a delta tau q
      ∂volume.prod volume) ≤
      |∫ q in pulsePairRectangle a delta tau,
        D (pulsePairPoint q)*pulseMomentWeight a delta tau q ∂volume.prod volume| := by
  have hDw : ContinuousOn
      (fun q => D (pulsePairPoint q)*pulseMomentWeight a delta tau q)
      (pulsePairRectangle a delta tau) :=
    (hD.comp pulsePairPoint_continuous.continuousOn (fun _ hq => pulsePairPoint_mem hq)).mul
      (pulseMomentWeight_continuous a delta tau).continuousOn
  have hDi : IntegrableOn
      (fun q => D (pulsePairPoint q)*pulseMomentWeight a delta tau q)
      (pulsePairRectangle a delta tau) (volume.prod volume) :=
    hDw.integrableOn_compact (pulsePairRectangle_isCompact a delta tau)
  have hwi : IntegrableOn (pulseMomentWeight a delta tau)
      (pulsePairRectangle a delta tau) (volume.prod volume) :=
    (pulseMomentWeight_continuous a delta tau).continuousOn.integrableOn_compact
    (pulsePairRectangle_isCompact a delta tau)
  have hmono : d0*(∫ q in pulsePairRectangle a delta tau, pulseMomentWeight a delta tau q
      ∂volume.prod volume) ≤ sigma*(∫ q in pulsePairRectangle a delta tau,
        D (pulsePairPoint q)*pulseMomentWeight a delta tau q ∂volume.prod volume) := by
    have h := integral_mono_ae (hwi.const_mul d0) (hDi.const_mul sigma) (by
      filter_upwards [ae_restrict_mem (pulsePairRectangle_isCompact a delta tau).measurableSet] with q hq
      have hp := mul_le_mul_of_nonneg_right (hfloor _ (pulsePairPoint_mem hq))
        (pulseMomentWeight_nonneg a delta tau q)
      simpa only [mul_assoc] using hp)
    simpa only [integral_const_mul] using h
  apply hmono.trans
  calc
    _ ≤ |sigma*(∫ q in pulsePairRectangle a delta tau,
        D (pulsePairPoint q)*pulseMomentWeight a delta tau q ∂volume.prod volume)| := le_abs_self _
    _ = _ := by rw [abs_mul,hsigma,one_mul]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseMomentError
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

theorem pulseWeightedMoment_bound {a delta tau B : ℝ} {f : Coord → ℝ}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau) (hB : 0 ≤ B)
    (hf : ∀ p ∈ pulseStrip a delta tau, |f p| ≤ B) :
    |pulseWeightedMoment a delta tau f| ≤
      B*(2*delta/tau)*(∫ x : ℝ, axisBump a x) := by
  have hmajor : IntegrableOn (fun q : ℝ × ℝ => B*axisBump a q.2)
      (pulsePairRectangle a delta tau) (volume.prod volume) :=
    ((continuous_const.mul ((axisBump_contDiff a).continuous.comp continuous_snd)).continuousOn).integrableOn_compact
      (pulsePairRectangle_isCompact a delta tau)
  have hpoint : ∀ᵐ q ∂(volume.prod volume).restrict (pulsePairRectangle a delta tau),
      ‖f (pulsePairPoint q)*pulseTest a tau q.2‖ ≤ B*axisBump a q.2 := by
    filter_upwards [ae_restrict_mem (pulsePairRectangle_isCompact a delta tau).measurableSet] with q hq
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hf _ (pulsePairPoint_mem hq)) (pulseTest_abs_le a tau q.2)
      (abs_nonneg _) hB
  have h := norm_integral_le_of_norm_le hmajor hpoint
  simp only [Real.norm_eq_abs,integral_const_mul] at h
  rw [pulse_spatial_mass_integral ha hd ht] at h
  simpa only [pulseWeightedMoment,mul_assoc] using h

theorem pulseWeightedMoment_integrable {a delta tau : ℝ} {f : Coord → ℝ}
    (hf : ContinuousOn f (pulseStrip a delta tau)) :
    IntegrableOn (fun q => f (pulsePairPoint q)*pulseTest a tau q.2)
      (pulsePairRectangle a delta tau) (volume.prod volume) :=
  ((hf.comp pulsePairPoint_continuous.continuousOn (fun _ hq => pulsePairPoint_mem hq)).mul
    ((pulseTest_continuous a tau).comp continuous_snd).continuousOn).integrableOn_compact
      (pulsePairRectangle_isCompact a delta tau)

theorem pulseWeightedMoment_sub {a delta tau : ℝ} {f h : Coord → ℝ}
    (hf : ContinuousOn f (pulseStrip a delta tau)) (hh : ContinuousOn h (pulseStrip a delta tau)) :
    pulseWeightedMoment a delta tau (fun p => f p-h p) =
      pulseWeightedMoment a delta tau f-pulseWeightedMoment a delta tau h := by
  unfold pulseWeightedMoment
  simp_rw [sub_mul]
  exact integral_sub (pulseWeightedMoment_integrable hf) (pulseWeightedMoment_integrable hh)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_MovingSourceBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

theorem movingSourceNorm_le_of_pointwise_bound
    {f : Coord → ℝ} {xl xr a b speed t F : ℝ}
    (hspeed : 0 ≤ speed) (ht : t ∈ Icc a b)
    (horder : inwardLeft xl a speed t ≤ inwardRight xr a speed t)
    (hF : 0 ≤ F)
    (hbound : ∀ p ∈ shrinkingSlab xl xr a b speed, |f p| ≤ F) :
    movingSourceNorm xl xr a speed f t ≤ F*Real.sqrt (xr-xl) := by
  let l := inwardLeft xl a speed t
  let r := inwardRight xr a speed t
  have hlen : r-l ≤ xr-xl := by
    have hi : 0 ≤ speed*(t-a) := mul_nonneg hspeed (sub_nonneg.mpr ht.1)
    dsimp [l,r,inwardLeft,inwardRight]
    linarith
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := l) (b := r) (C := F^2) (f := fun x => f (coordinatePoint x t)^2) (by
      intro x hx
      have hx0 : x ∈ Ioc l r := by
        rw [uIoc_of_le (show l ≤ r from horder)] at hx
        exact hx
      have hb := hbound _ (point_mem_shrinkingSlab ht ⟨hx0.1.le,hx0.2⟩)
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hF).mpr hb)
  have hsquare : (∫ x in l..r, f (coordinatePoint x t)^2) ≤ F^2*(xr-xl) := by
    apply (le_abs_self _).trans
    apply hi.trans
    rw [abs_of_nonneg (sub_nonneg.mpr horder)]
    exact mul_le_mul_of_nonneg_left hlen (sq_nonneg F)
  have hsqrt := Real.sqrt_le_sqrt hsquare
  simpa only [movingSourceNorm,movingIntervalIntegral,l,r,
    Real.sqrt_mul (sq_nonneg F),Real.sqrt_sq hF] using hsqrt

theorem integrated_movingSourceNorm_le_of_pointwise_bound
    {f : Coord → ℝ} {xl xr a b speed F : ℝ}
    (hab : a ≤ b) (hspeed : 0 ≤ speed) (hF : 0 ≤ F)
    (horder : ∀ t ∈ Icc a b, inwardLeft xl a speed t ≤ inwardRight xr a speed t)
    (hbound : ∀ p ∈ shrinkingSlab xl xr a b speed, |f p| ≤ F) :
    (∫ t in a..b, movingSourceNorm xl xr a speed f t) ≤
      F*Real.sqrt (xr-xl)*(b-a) := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := F*Real.sqrt (xr-xl))
    (f := movingSourceNorm xl xr a speed f) (by
      intro t ht
      have ht0 : t ∈ Ioc a b := by simpa only [uIoc_of_le hab] using ht
      have ht1 : t ∈ Icc a b := ⟨ht0.1.le,ht0.2⟩
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ movingSourceNorm xl xr a speed f t from Real.sqrt_nonneg _)]
      exact movingSourceNorm_le_of_pointwise_bound hspeed ht1 (horder t ht1) hF hbound)
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] using hi)

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonGradientSlice
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

theorem fixed_slice_gradient_le_moving_energy
    {S v : Coord → ℝ} {V : Set Coord} {xl xr a speed t pulseRadius s0 : ℝ}
    (hV : IsOpen V) (hS : ContinuousOn S V) (hv : ContDiffOn ℝ ∞ v V)
    (hs0 : 0 < s0) (hpulse : 0 ≤ pulseRadius)
    (hleft : inwardLeft xl a speed t ≤ -pulseRadius)
    (hright : pulseRadius ≤ inwardRight xr a speed t)
    (hmem : ∀ x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t),
      coordinatePoint x t ∈ V)
    (hfloor : ∀ x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t),
      s0 ≤ S (coordinatePoint x t)) (i : Fin 2) :
    Real.sqrt (∫ x in Icc (-pulseRadius) pulseRadius, (coordPartial i v (boxPoint x t))^2) ≤
      Real.sqrt (2*(1+1/s0))*Real.sqrt (movingEnergy xl xr a speed S v t) := by
  let l := inwardLeft xl a speed t
  let r := inwardRight xr a speed t
  let K := 2*(1+1/s0)
  have hlr : l ≤ r := hleft.trans ((by linarith : -pulseRadius ≤ pulseRadius).trans hright)
  have hK : 0 ≤ K := by dsimp [K] <;> positivity
  have hpointContinuous : Continuous (fun x : ℝ => coordinatePoint x t) := by
    unfold coordinatePoint
    fun_prop
  have hvi : ContinuousOn (fun x => coordPartial i v (coordinatePoint x t)) (Icc l r) :=
    (partial_contDiffOn hv hV i).continuousOn.comp hpointContinuous.continuousOn hmem
  have hvt : ContinuousOn (fun x => coordPartial 1 v (coordinatePoint x t)) (Icc l r) :=
    (partial_contDiffOn hv hV 1).continuousOn.comp hpointContinuous.continuousOn hmem
  have hvx : ContinuousOn (fun x => coordPartial 0 v (coordinatePoint x t)) (Icc l r) :=
    (partial_contDiffOn hv hV 0).continuousOn.comp hpointContinuous.continuousOn hmem
  have hSc : ContinuousOn (fun x => S (coordinatePoint x t)) (Icc l r) :=
    hS.comp hpointContinuous.continuousOn hmem
  have he : ContinuousOn (fun x => energyDensity S v (coordinatePoint x t)) (Icc l r) :=
    ((hvt.pow 2).add (hSc.mul (hvx.pow 2))).div_const 2
  have hsmall : (∫ x in -pulseRadius..pulseRadius, (coordPartial i v (coordinatePoint x t))^2) ≤
      ∫ x in l..r, (coordPartial i v (coordinatePoint x t))^2 :=
    intervalIntegral.integral_mono_interval hleft (by linarith) hright
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      ((hvi.pow 2).intervalIntegrable_of_Icc hlr)
  have henergy : (∫ x in l..r, (coordPartial i v (coordinatePoint x t))^2) ≤
      K*movingEnergy xl xr a speed S v t := by
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hlr
      ((hvi.pow 2).intervalIntegrable_of_Icc hlr)
      ((continuousOn_const.mul he).intervalIntegrable_of_Icc hlr) (fun x hx => by
        have hscalar := scalar_gradient_le_energy hs0 (hfloor x hx)
          (a := coordPartial 1 v (coordinatePoint x t)) (b := coordPartial 0 v (coordinatePoint x t))
        have hi : (coordPartial i v (coordinatePoint x t))^2 ≤
            (coordPartial 1 v (coordinatePoint x t))^2+(coordPartial 0 v (coordinatePoint x t))^2 := by
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> nlinarith [sq_nonneg (coordPartial 0 v (coordinatePoint x t)),
            sq_nonneg (coordPartial 1 v (coordinatePoint x t))]
        exact hi.trans hscalar)
    dsimp only [Pi.pow_apply,Pi.mul_apply] at hmono
    simpa only [intervalIntegral.integral_const_mul,movingEnergy,movingIntervalIntegral,l,r,K] using hmono
  have hroot := Real.sqrt_le_sqrt (hsmall.trans henergy)
  rw [Real.sqrt_mul hK] at hroot
  have hpoint : (fun x => coordPartial i v (coordinatePoint x t)^2) =
      (fun x => coordPartial i v (boxPoint x t)^2) := by
    funext x
    have he : coordinatePoint x t=boxPoint x t := by ext j; fin_cases j <;> simp [coordinatePoint,boxPoint]
    rw [he]
  simpa only [intervalIntegral.integral_of_le (by linarith : -pulseRadius ≤ pulseRadius),
    ← integral_Icc_eq_integral_Ioc,hpoint,K] using hroot

end SmoothLocal.Hyperbolic

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

theorem actual_testMetric_eventuallyEq_on_upper_cap
    {G Z d c e0 kappa q0 L r delta tau : ℝ}
    {g : MetricField} {U W : Set Coord} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hh : CapInductionHeight g U Z c e0 z)
    (hf : CapInductionFlow g U G Z d c e0 kappa z Y W)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hr : 0 < r) (hLr : L*r ≤ 1/20)
    (hq0 : |q0| ≤ 1/20) (hcenter : |hessianQuotient g z 0-q0| ≤ 1/(100*L))
    (hrsmall : heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L))
    (hdelta : 0 < delta) (htau : 0 < tau) (hwidth : delta/(2*tau) ≤ r/4)
    (gStar : MetricField) (N : ℕ) (R : UpperCapRectangle (r/2))
    {p : Coord} (hp : p ∈ R.image Y) :
    testMetric gStar q0 (L*r/16) N delta tau =ᶠ[𝓝 p] gStar := by
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  have hpartial (v : Coord) (hv : v ∈ modelSquare) (i : Fin 2) :
      |coordPartial i (hessianQuotient g z) v| ≤ M := hf.quotientBound [i] (by norm_num) v hv
  obtain ⟨v,hv,rfl⟩ := hp
  have hseed : r/2 ≤ |v 1| := by
    have hbottom : R.bottom ≤ v 1 := hv.2.1
    have hfloor := R.bottom_gt
    have habs := le_abs_self (v 1)
    linarith
  exact metric_add_eventuallyEq_of_not_mem_tsupport gStar (pulseTensor q0 (L*r/16) N delta tau)
    (pulseTensor_not_tsupport_exterior_seed hf.quotientSmooth hf.domainOpen hf.squareSubset
      hf.continuous hf.range hf.start hf.ode hh.quotient hM hL hr hpartial hq0 hcenter
      (by linarith : L*r < 2) (by positivity : 0 < L*r/16)
      (by nlinarith [mul_pos hL hr] : L*r/16 ≤ L*r) hrsmall hdelta htau hwidth N
      (R.region_subset_domain hv) hseed)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ShearedPulseRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.Hyperbolic

theorem pulseRectangle_mem_shearedModelSquare
    {q0 L r delta tau x t : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20)
    (hwidth : delta/tau ≤ r) (hx : |x| ≤ L*r/2)
    (ht : t ∈ Icc (-delta/tau) (delta/tau)) :
    (![x,t] : Coord) ∈ shearedModelSquare q0 := by
  apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
  constructor
  · exact hx.trans (by nlinarith [mul_pos hL hr])
  · exact (abs_le.mpr ⟨by simpa only [neg_div] using ht.1, ht.2⟩).trans hwidth

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_UniformTaylorDenominator
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

theorem stateBaseCompact_mem_of_norm {w : DarbouxState} {S : Set Coord} {M : ℝ}
    (hp : statePoint w ∈ S) (hw : ‖w‖ ≤ M) : w ∈ stateBaseCompact S M := by
  refine ⟨hp, ?_⟩
  constructor <;> intro i
  · exact (abs_le.mp ((norm_le_pi_norm w i).trans hw)).1
  · exact (abs_le.mp ((norm_le_pi_norm w i).trans hw)).2

end SmoothLocal.Taylor

end

end OAI
end


