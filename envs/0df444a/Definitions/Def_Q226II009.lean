-- Prove2me | Definitions.Def_Q226II009
-- name    : Q226II009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:42:01.604268+00:00
-- url     : https://prove2.me/theorems/0896ac43-5643-400b-9429-6c5d0cbd7531
-- title:
--   Definitions bundle Q226II009 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 198 declarations of OpenAI's Lean: 25 definitions, 1 inductive type or structure and 172 theorems. The definitions and types are `OAI.SmoothLocal.Geometry.curvatureLowerTerm`, `OAI.SmoothLocal.Geometry.patchTensorIndex`, `OAI.SmoothLocal.HighEquation.metricComparisonSource`, `OAI.SmoothLocal.HighEquation.metricQSpatialBundle`, `OAI.SmoothLocal.HighEquation.universalMetricQ`, `OAI.SmoothLocal.HighEquation.universalMetricQDomain`, `OAI.SmoothLocal.HighEquation.universalMetricQTube`, `OAI.SmoothLocal.HighEquation.universalQCurvature`, `OAI.SmoothLocal.HighEquation.universalQDenominator`, `OAI.SmoothLocal.HighEquation.universalQNumerator`, `OAI.SmoothLocal.HighEquation.universalQRaw`, `OAI.SmoothLocal.Pulse.QPulsePointBounds`, `OAI.SmoothLocal.Pulse.actualComparisonSource`, `OAI.SmoothLocal.Pulse.actualShearedQForcing`, `OAI.SmoothLocal.Pulse.actualShearedQLeading`, `OAI.SmoothLocal.Pulse.qFirstBundle`, `OAI.SmoothLocal.Pulse.qPulseFirstJetBudget`, `OAI.SmoothLocal.Pulse.scalarPulseDerivativeBound`, `OAI.SmoothLocal.Pulse.scalarPulseFirstJetBound`, `OAI.SmoothLocal.Pulse.scalarPulseFirstJetBudget`, `OAI.SmoothLocal.Pulse.shearTimeFactor`, `OAI.SmoothLocal.Pulse.thetaPulseLowerDifference`, `OAI.SmoothLocal.Taylor.comparisonDomain`, `OAI.SmoothLocal.Taylor.correctionState`, `OAI.SmoothLocal.Taylor.nextTaylorCoefficient`, `OAI.SmoothLocal.Taylor.taylorApproximation`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Assembly_EnumeratedPatchTensors`, `IsometricImmersion_Assembly_SupportedMetricJets`, `IsometricImmersion_Assembly_SupportedPerturbations`, `IsometricImmersion_Calculus_BoundedClassInitialJet`, `IsometricImmersion_Calculus_HorizontalJetCalculus`, `IsometricImmersion_Calculus_MovingIntervalCalculus`, `IsometricImmersion_Calculus_ShearHeightJets`, `IsometricImmersion_Calculus_ShearMetricFullJets`, `IsometricImmersion_Calculus_ShearMetricJets`, `IsometricImmersion_Caps_PulseCapSeparation`, `IsometricImmersion_Caps_PulseReflection`, `IsometricImmersion_Caps_QPointwiseCauchyJets`, `IsometricImmersion_Comparison_ActualComparisonEnergy`, `IsometricImmersion_Comparison_ActualComparisonSource`, `IsometricImmersion_Comparison_ComparisonCoefficientBounds`, `IsometricImmersion_Comparison_QFirstJetComparison`, `IsometricImmersion_Comparison_QMetricApproximationInputs`, `IsometricImmersion_Comparison_ShearFirstJetComparison`, `IsometricImmersion_Coordinates_ActualShearHyperbolicity`, `IsometricImmersion_Coordinates_CoordinateSwap`, `IsometricImmersion_Curvature_CurvatureLowerTube`, `IsometricImmersion_Curvature_PatchCurvatureProfiles`, `IsometricImmersion_Darboux_CurvaturePrincipalPart`, `IsometricImmersion_Darboux_QClosedStripMargins`, `IsometricImmersion_Darboux_QFirstJetEnergy`, `IsometricImmersion_Darboux_QFirstJetFunctions`, `IsometricImmersion_Darboux_QFirstSpatialBounds`, `IsometricImmersion_Darboux_QHighEquation`, `IsometricImmersion_Darboux_QInitialEnergy`, `IsometricImmersion_Darboux_QLowActualBounds`, `IsometricImmersion_Darboux_QReferenceInitialTolerance`, `IsometricImmersion_Darboux_QResidualActive`, `IsometricImmersion_Darboux_QResidualFactors`, `IsometricImmersion_Darboux_QResidualL2`, `IsometricImmersion_Darboux_QSpatialJets`, `IsometricImmersion_Darboux_QStripJetControl`, `IsometricImmersion_Energy_HyperbolicEnergyDensity`, `IsometricImmersion_Energy_MovingIntervalSobolev`, `IsometricImmersion_Energy_MovingSlabEnergy`, `IsometricImmersion_Estimates_ActualQWeightedRemainder`, `IsometricImmersion_Estimates_UniversalQRaw`, `IsometricImmersion_Immersions_ActualShearHeight`, `IsometricImmersion_Metrics_LocalMetricQActive`, `IsometricImmersion_Metrics_LocalMetricQFull`, `IsometricImmersion_Metrics_MetricQSpatialBundle`, `IsometricImmersion_Metrics_StateCoefficientTube`, `IsometricImmersion_Metrics_UniversalMetricQ`, `IsometricImmersion_Metrics_WarpedMetric`, `IsometricImmersion_Pulses_ActualForcingCoefficient`, `IsometricImmersion_Pulses_ActualQPulseForcing`, `IsometricImmersion_Pulses_ForcingCoefficientSign`, `IsometricImmersion_Pulses_PulseCurvaturePrincipal`, `IsometricImmersion_Pulses_PulseFirstJetControl`, `IsometricImmersion_Pulses_PulseOperatorMoment`, `IsometricImmersion_Pulses_PulseProfiles`, `IsometricImmersion_Pulses_PulseSecondXi`, `IsometricImmersion_Pulses_PulseSpatialParts`, `IsometricImmersion_Pulses_PulseTemporalMoment`, `IsometricImmersion_Pulses_PulseTemporalParts`, `IsometricImmersion_Pulses_QPulseFirstJetBudget`, `IsometricImmersion_Pulses_ShearedPulseRegions`, `IsometricImmersion_Taylor_FiniteTaylorComparison`, `IsometricImmersion_Taylor_TaylorCauchyData`, `IsometricImmersion_Taylor_TaylorInitialStateBound`, `IsometricImmersion_Taylor_TaylorJetStability`, `IsometricImmersion_Taylor_TaylorQJetBounds`, `IsometricImmersion_Taylor_TaylorResidual`, `IsometricImmersion_Taylor_TaylorSeparatedProduct`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II003`, `Q226II004`, `Q226II005` and `Q226II006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q226II011`, `Q226II012` and `Q226II013`.
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
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.Count
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Countable
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
import Definitions.Def_Q226II003
import Definitions.Def_Q226II004
import Definitions.Def_Q226II005
import Definitions.Def_Q226II006

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_PatchCurvatureProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter Metric

namespace SmoothLocal.Geometry
open SmoothLocal.Weighted SmoothLocal.Model

theorem patchBoxCutoff_one {p : Coord} (hp : ‖p‖ ≤ 13 / 4) : patchBoxCutoff p = 1 := by
  have hb (i : Fin 2) : |p i| ≤ 13 / 4 := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm p i).trans hp
  simp only [patchBoxCutoff, patchAxisCutoff_one (hb 0), patchAxisCutoff_one (hb 1), one_mul]

theorem localPatchProfile_eq_model {p : Coord} (hp : ‖p‖ ≤ 13 / 4) :
    localPatchProfile p = (p 0) ^ 2 - modelProfile (p 1) := by
  simp only [localPatchProfile, patchBoxCutoff_one hp, modelCurvature, one_mul]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_WarpedMetric
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

theorem warpedMetric_smoothPositiveOn {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hne : ∀ p ∈ U, f p ≠ 0) :
    SmoothPositiveOn (warpedMetric f) U := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j
    · simpa using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Coord => (1 : ℝ)) U)
    · simpa using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Coord => (0 : ℝ)) U)
    · simpa using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Coord => (0 : ℝ)) U)
    · simpa using hf.pow 2
  · intro p hp
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · simp
    · simpa using sq_pos_of_ne_zero (hne p hp)

end SmoothLocal.Geometry

end

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

theorem supportedTensor_iteratedFDeriv_eval_continuous (k : ℕ) :
    Continuous (fun a : SupportedTensor × Coord => iteratedFDeriv ℝ k a.1 a.2) := by
  have h := ((ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k).continuous.comp
    (continuous_fst : Continuous (Prod.fst : SupportedTensor × Coord → SupportedTensor))).eval
      continuous_snd
  simpa only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply] using h

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

theorem patchAddressMatrix_isUnit (a : PatchAddress) : IsUnit (patchAddressMatrix a) :=
  orientedPatchMatrix_isUnit a.1 a.2.1 a.2.2.1

def patchTensorIndex (a : PatchAddress) : ℕ :=
  Encodable.encode (Sum.inr a : AssemblyProfileIndex)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_SupportedMetricJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

theorem supportedTensor_coeff_iteratedFDeriv (η : SupportedTensor) (k : ℕ)
    (p : Coord) (v : Fin k → Coord) (i j : Fin 2) :
    iteratedFDeriv ℝ k (fun q => η q i j) p v = (iteratedFDeriv ℝ k η p v) i j := by
  change iteratedFDeriv ℝ k (metricCoefficientCLM i j ∘ η) p v =
    metricCoefficientCLM i j (iteratedFDeriv ℝ k η p v)
  have he := (metricCoefficientCLM i j).iteratedFDeriv_comp_left (x := p) (i := k)
    η.contDiff.contDiffAt (le_of_lt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k))
  exact congrArg (fun L : Coord [×k]→L[ℝ] ℝ => L v) he

theorem supportedTensor_coordPartial_eq_jet (η : SupportedTensor)
    (p : Coord) (d i j : Fin 2) :
    coordPartial d (fun q => η q i j) p =
      (iteratedFDeriv ℝ 1 η p (fun _ => Pi.single d 1)) i j := by
  rw [← supportedTensor_coeff_iteratedFDeriv]
  simp only [iteratedFDeriv_one_apply, coordPartial]

theorem supportedTensor_second_coordPartial_eq_jet (η : SupportedTensor)
    (p : Coord) (d e i j : Fin 2) :
    coordPartial d (coordPartial e (fun q => η q i j)) p =
      (iteratedFDeriv ℝ 2 η p ![Pi.single d 1, Pi.single e 1]) i j := by
  have hs : ContDiff ℝ ∞ (fun q => η q i j) :=
    (metricCoefficientCLM i j).contDiff.comp η.contDiff
  rw [← supportedTensor_coeff_iteratedFDeriv, iteratedFDeriv_two_apply,
    second_coordPartial_eq_fderiv hs.contDiffOn isOpen_univ (mem_univ p)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem supportedTensor_coeff_eval_joint_continuous (i j : Fin 2) :
    Continuous (fun a : SupportedTensor × Coord => a.1 a.2 i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_eval)

theorem supportedTensor_coordPartial_joint_continuous (d i j : Fin 2) :
    Continuous (fun a : SupportedTensor × Coord =>
      coordPartial d (fun q => a.1 q i j) a.2) := by
  have hc := (supportedTensor_iteratedFDeriv_eval_continuous 1).eval
    (continuous_const (y := ((fun _ : Fin 1 => Pi.single d (1 : ℝ)) : Fin 1 → Coord)))
  have he := (continuous_apply j).comp ((continuous_apply i).comp hc)
  simp only [supportedTensor_coordPartial_eq_jet]
  exact he

theorem supportedTensor_second_coordPartial_joint_continuous (d e i j : Fin 2) :
    Continuous (fun a : SupportedTensor × Coord =>
      coordPartial d (coordPartial e (fun q => a.1 q i j)) a.2) := by
  have hc := (supportedTensor_iteratedFDeriv_eval_continuous 2).eval
    (continuous_const (y := (![Pi.single d 1, Pi.single e 1] : Fin 2 → Coord)))
  have he := (continuous_apply j).comp ((continuous_apply i).comp hc)
  simp only [supportedTensor_second_coordPartial_eq_jet]
  exact he

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_CoordinateSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

theorem swappedMetric_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) :
    SmoothPositiveOn (swappedMetric g) (coordinateSwap ⁻¹' U) :=
  affinePullbackMetric_smoothPositive hg 0 coordinateSwapMatrix
    (Matrix.mulVec_injective_of_isUnit coordinateSwapMatrix_isUnit)

theorem gaussianCurvature_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) :
    gaussianCurvature (swappedMetric g) p = gaussianCurvature g (coordinateSwap p) :=
  gaussianCurvature_affinePullback hg hU 0 coordinateSwapMatrix
    coordinateSwapMatrix_isUnit p hp

end SmoothLocal.Geometry

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

theorem forcingCoefficient_eq_energy {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (z : Coord → ℝ) {p : Coord} (hp : p ∈ U) :
    forcingCoefficient g z p =
      heightEnergy g z p / (2 * (g p).det * covHessian g z p 0 0) := by
  unfold forcingCoefficient heightEnergy
  have hd := metricDet_ne_zero hg hp
  by_cases hh : covHessian g z p 0 0 = 0
  · simp [hh]
  · field_simp [hd, hh]

theorem forcingCoefficient_abs_eq {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U)
    (hE : 0 ≤ heightEnergy g z p) :
    |forcingCoefficient g z p| =
      heightEnergy g z p / (2 * (g p).det * |covHessian g z p 0 0|) := by
  rw [forcingCoefficient_eq_energy hg z hp, abs_div, abs_of_nonneg hE]
  simp only [abs_mul, abs_of_pos (hg.2 p hp).det_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem forcingCoefficient_bounds {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U)
    {e E d D c C : ℝ} (he : 0 < e) (hd : 0 < d) (hc : 0 < c)
    (hE : e ≤ heightEnergy g z p) (hEup : heightEnergy g z p ≤ E)
    (hdet : d ≤ (g p).det) (hdetup : (g p).det ≤ D)
    (hxx : c ≤ |covHessian g z p 0 0|) (hxxup : |covHessian g z p 0 0| ≤ C) :
    0 < e / (2 * D * C) ∧
      e / (2 * D * C) ≤ |forcingCoefficient g z p| ∧
      |forcingCoefficient g z p| ≤ E / (2 * d * c) := by
  have hDp : 0 < D := hd.trans_le (hdet.trans hdetup)
  have hCp : 0 < C := hc.trans_le (hxx.trans hxxup)
  have hgdet : 0 < (g p).det := hd.trans_le hdet
  have hgxx : 0 < |covHessian g z p 0 0| := hc.trans_le hxx
  have hden : 0 < 2 * (g p).det * |covHessian g z p 0 0| := by positivity
  have hdenlo : 2 * d * c ≤ 2 * (g p).det * |covHessian g z p 0 0| :=
    mul_le_mul (mul_le_mul_of_nonneg_left hdet (by norm_num)) hxx hc.le
      (by positivity)
  have hdenup : 2 * (g p).det * |covHessian g z p 0 0| ≤ 2 * D * C :=
    mul_le_mul (mul_le_mul_of_nonneg_left hdetup (by norm_num)) hxxup hgxx.le
      (by positivity)
  rw [forcingCoefficient_abs_eq hg hp (he.le.trans hE)]
  refine ⟨by positivity, ?_, ?_⟩
  · exact div_le_div₀ (he.le.trans hE) hE hden hdenup
  · exact div_le_div₀ (he.le.trans (hE.trans hEup)) hEup (by positivity) hdenlo

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_CurvaturePrincipalPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def curvatureLowerTerm (g : MetricField) (p : Coord) : ℝ :=
  curvatureLowerJet (g p) (metricFirstJet g p)

theorem metric_coeff_second_partial_symm {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (d e i j : Fin 2) :
    coordPartial d (coordPartial e (fun q => g q i j)) p =
      coordPartial d (coordPartial e (fun q => g q j i)) p := by
  have he : coordPartial e (fun q => g q i j) =ᶠ[𝓝 p]
      coordPartial e (fun q => g q j i) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact metric_coeff_partial_symm hg hU hq e i j
  exact coordPartial_eq_of_eventuallyEq he d

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseProfiles
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply _root_.OAI.SmoothLocal.Pulse.inverseShearMatrix_det
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem shear_inverse (q0 : ℝ) (p : Coord) :
    shearCoordinates q0 (inverseShearCoordinates q0 p) = p := by
  ext i
  fin_cases i <;> simp [shearCoordinates, inverseShearCoordinates]

theorem pulseTensor_inverseShear (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    affinePullbackMetric (pulseTensor q0 a N delta tau) 0 (inverseShearMatrix q0) p =
      !![0, 0; 0, pulseScalar a N delta tau p] := by
  rw [affinePullbackMetric, ← inverseShearCoordinates_eq_affine]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pulseTensor, shear_inverse, inverseShearMatrix, thetaCovector,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem testMetric_inverseShear (gStar : MetricField) (q0 a : ℝ) (N : ℕ)
    (delta tau : ℝ) (p : Coord) :
    affinePullbackMetric (testMetric gStar q0 a N delta tau) 0 (inverseShearMatrix q0) p =
      affinePullbackMetric gStar 0 (inverseShearMatrix q0) p +
        !![0, 0; 0, pulseScalar a N delta tau p] := by
  rw [← pulseTensor_inverseShear q0 a N delta tau p]
  simp only [affinePullbackMetric, testMetric, Pi.add_apply, mul_add, add_mul]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseCurvaturePrincipal
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def thetaPulseLowerDifference (g : MetricField) (f : Coord → ℝ) (p : Coord) : ℝ :=
  curvatureLowerJet (g p + !![0,0;0,f p])
    (metricFirstJet g p + thetaPulseFirstJet f p) -
      curvatureLowerJet (g p) (metricFirstJet g p)

theorem metricFirstJet_thetaPulseMetric {g : MetricField} {f : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) :
    metricFirstJet (thetaPulseMetric g f) p = metricFirstJet g p + thetaPulseFirstJet f p := by
  funext d i j
  have hgD : DifferentiableAt ℝ (fun q => g q i j) p :=
    ((hg.1 i j).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hfD : DifferentiableAt ℝ f p :=
    (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  by_cases hij : i=1 ∧ j=1
  · have he : (fun q => thetaPulseMetric g f q i j) = (fun q => g q i j+f q) := by
      funext q
      simp only [thetaPulseMetric_entry,ite_eq_left hij]
    change coordPartial d (fun q => thetaPulseMetric g f q i j) p = _
    rw [he,HessianCalculus.coordPartial_add_at hgD hfD d]
    simp only [Pi.add_apply,Matrix.add_apply,metricFirstJet,thetaPulseFirstJet,ite_eq_left hij]
  · have he : (fun q => thetaPulseMetric g f q i j) = (fun q => g q i j) := by
      funext q
      simp only [thetaPulseMetric_entry,ite_eq_right hij,add_zero]
    change coordPartial d (fun q => thetaPulseMetric g f q i j) p = _
    rw [he]
    simp only [Pi.add_apply,Matrix.add_apply,metricFirstJet,thetaPulseFirstJet,ite_eq_right hij,add_zero]

theorem secondCoordPartial_add {f h : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j (fun q => f q+h q)) p =
      coordPartial i (coordPartial j f) p + coordPartial i (coordPartial j h) p := by
  have he : coordPartial j (fun q => f q+h q) =ᶠ[𝓝 p]
      (fun q => coordPartial j f q+coordPartial j h q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact HessianCalculus.coordPartial_add_at
      ((hf.contDiffAt (hU.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      ((hh.contDiffAt (hU.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) j
  rw [coordPartial_eq_of_eventuallyEq he i]
  exact HessianCalculus.coordPartial_add_at
    (((partial_contDiffOn hf hU j).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (((partial_contDiffOn hh hU j).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) i

theorem thetaPulseLowerDifference_eq {g : MetricField} {f : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) :
    thetaPulseLowerDifference g f p =
      curvatureLowerTerm (thetaPulseMetric g f) p-curvatureLowerTerm g p := by
  simp only [curvatureLowerTerm,metricFirstJet_thetaPulseMetric hg hf hU hp,
    thetaPulseMetric,thetaPulseLowerDifference]

theorem metricInShearCoordinates_test (gStar : MetricField) (q0 a : ℝ) (N : ℕ)
    (delta tau : ℝ) :
    metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0 =
      thetaPulseMetric (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau) := by
  funext p
  exact testMetric_inverseShear gStar q0 a N delta tau p

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_CurvatureLowerTube
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

theorem thetaPulseLowerDifference_eq_firstFunction (g : MetricField) (f : Coord → ℝ) (p : Coord) :
    thetaPulseLowerDifference g f p =
      curvatureFirstFunction (actualCurvatureFirstInput g p+thetaCurvatureFirstIncrement f p)-
        curvatureFirstFunction (actualCurvatureFirstInput g p) := rfl

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseFirstJetControl
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

def scalarPulseDerivativeBound (a : ℝ) (ha : 0 < a) (delta : ℝ) (k : ℕ) : ℝ :=
  pulseCoreDerivativeBound a ha k * pulseScaleBound 0 delta ^ k

theorem scalarPulseDerivativeBound_nonneg {a : ℝ} (ha : 0 < a) (delta : ℝ) (k : ℕ) :
    0 ≤ scalarPulseDerivativeBound a ha delta k :=
  mul_nonneg (pulseCoreDerivativeBound_nonneg ha k) (pow_nonneg (pulseScaleBound_pos 0 delta).le k)

theorem pulseScalar_eq_core (a : ℝ) (N : ℕ) (delta tau : ℝ) :
    pulseScalar a N delta tau = fun p => (1/tau^N) • pulseCore 0 a delta tau p := by
  funext p
  simp only [pulseScalar,pulseCore,xiCLM,thetaCLM,temporalCutoff,
    add_apply,smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,zero_mul,add_zero]
  have ht : tau/delta*p 1 = tau*p 1/delta := by ring
  rw [ht]
  ring

theorem pulseScalar_derivative_le {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (pulseScalar a N delta tau) p‖ ≤
      scalarPulseDerivativeBound a ha delta k * tau^k/tau^N := by
  have ht0 : 0 < tau := zero_lt_one.trans_le ht
  rw [pulseScalar_eq_core]
  rw [iteratedFDeriv_const_smul_apply' (i := k) (a := (1/tau^N : ℝ))
    ((pulseCore_contDiff 0 a delta tau).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
    norm_smul,Real.norm_of_nonneg (div_nonneg zero_le_one (pow_nonneg ht0.le N))]
  calc
    _ ≤ (1/tau^N)*(pulseCoreDerivativeBound a ha k*(tau*pulseScaleBound 0 delta)^k) :=
      mul_le_mul_of_nonneg_left (pulseCore_derivative_le ha 0 delta ht k p)
        (div_nonneg zero_le_one (pow_nonneg ht0.le N))
    _ = _ := by rw [mul_pow]; unfold scalarPulseDerivativeBound; ring

def scalarPulseFirstJetBound (a : ℝ) (ha : 0 < a) (delta : ℝ) : ℝ :=
  max (scalarPulseDerivativeBound a ha delta 0) (scalarPulseDerivativeBound a ha delta 1)

theorem scalarPulseFirstJetBound_nonneg {a : ℝ} (ha : 0 < a) (delta : ℝ) :
    0 ≤ scalarPulseFirstJetBound a ha delta :=
  (scalarPulseDerivativeBound_nonneg ha delta 0).trans (le_max_left _ _)

def scalarPulseFirstJetBudget (a : ℝ) (ha : 0 < a) (N : ℕ) (delta tau : ℝ) : ℝ :=
  scalarPulseFirstJetBound a ha delta * tau/tau^N

theorem scalarPulseFirstJetBudget_nonneg {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) : 0 ≤ scalarPulseFirstJetBudget a ha N delta tau :=
  div_nonneg (mul_nonneg (scalarPulseFirstJetBound_nonneg ha delta) (zero_le_one.trans ht))
    (pow_nonneg (zero_le_one.trans ht) N)

theorem pulseScalar_first_jet_bounds {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (p : Coord) :
    |pulseScalar a N delta tau p| ≤ scalarPulseFirstJetBudget a ha N delta tau ∧
      ∀ i, |coordPartial i (pulseScalar a N delta tau) p| ≤ scalarPulseFirstJetBudget a ha N delta tau := by
  have ht0 : 0 ≤ tau := zero_le_one.trans ht
  have hden : 0 ≤ tau^N := pow_nonneg ht0 N
  have hB0 : scalarPulseDerivativeBound a ha delta 0 ≤ scalarPulseFirstJetBound a ha delta :=
    le_max_left _ _
  have hB1 : scalarPulseDerivativeBound a ha delta 1 ≤ scalarPulseFirstJetBound a ha delta :=
    le_max_right _ _
  constructor
  · have h := pulseScalar_derivative_le ha N delta ht 0 p
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,mul_one] at h
    exact h.trans (div_le_div_of_nonneg_right
      (hB0.trans (le_mul_of_one_le_right (scalarPulseFirstJetBound_nonneg ha delta) ht)) hden)
  · intro i
    have h := (norm_iteratedCoordPartial_le_jet
      (pulseScalar_contDiff a N delta tau).contDiffOn isOpen_univ [i] (mem_univ p)).trans
        (pulseScalar_derivative_le ha N delta ht 1 p)
    simp only [iteratedCoordPartial,Real.norm_eq_abs,pow_one] at h
    exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB1 ht0) hden)

theorem thetaPulse_first_increment_bound {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (p : Coord) :
    ‖thetaCurvatureFirstIncrement (pulseScalar a N delta tau) p‖ ≤
      scalarPulseFirstJetBudget a ha N delta tau :=
  thetaCurvatureFirstIncrement_norm_le _ p (scalarPulseFirstJetBudget_nonneg ha N delta ht)
    (pulseScalar_first_jet_bounds ha N delta ht p).1 (pulseScalar_first_jet_bounds ha N delta ht p).2

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

theorem coordPartial_xi_eq_line_deriv {f : Coord → ℝ}
    (hf : Differentiable ℝ f) (p : Coord) :
    coordPartial 0 f p = deriv (fun x => f (coordinatePoint x (p 1))) (p 0) := by
  have h := (hf (coordinatePoint (p 0) (p 1))).hasFDerivAt.comp_hasDerivAt
    (p 0) (point_hasDerivAt_t (p 0) (p 1))
  simpa only [point_eta,coordPartial,Function.comp_def] using h.deriv.symm

theorem pulseLine_hasDerivAt (a : ℝ) (N : ℕ) (delta tau x y : ℝ) :
    HasDerivAt (fun u => pulseScalar a N delta tau (coordinatePoint u y))
      ((1/tau^N)*temporalCutoff (tau*y/delta)*
        (deriv (axisBump a) x*Real.cos (tau*x)-tau*axisBump a x*Real.sin (tau*x))) x := by
  have hχ := ((axisBump_contDiff a).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasDerivAt
  have hc := (Real.hasDerivAt_cos (tau*x)).comp x ((hasDerivAt_id x).const_mul tau)
  have h := (((hχ.const_mul (1/tau^N)).mul_const
    (temporalCutoff (tau*y/delta))).mul hc)
  simp only [Function.comp_def, Pi.mul_def, mul_one] at h
  convert h using 1 <;>
    (first | rfl | (funext u; simp [pulseScalar, coordinatePoint]) | ring)

theorem pulseScalar_xi (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    coordPartial 0 (pulseScalar a N delta tau) p =
      (1/tau^N)*temporalCutoff (tau*p 1/delta)*
        (deriv (axisBump a) (p 0)*Real.cos (tau*p 0)-
          tau*axisBump a (p 0)*Real.sin (tau*p 0)) := by
  rw [coordPartial_xi_eq_line_deriv ((pulseScalar_contDiff a N delta tau).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  exact (pulseLine_hasDerivAt a N delta tau (p 0) (p 1)).deriv

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QFirstJetFunctions
attribute [-simp] _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero
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

def qFirstBundle (g : MetricField) (w : DarbouxState) : QFirstInput :=
  (actualCurvatureFirstInput g (statePoint w),w)

theorem qFirstDet_bundle (g : MetricField) (w : DarbouxState) :
    qFirstDet (qFirstBundle g w) = (g (statePoint w)).det := rfl
theorem qFirstXX_bundle (g : MetricField) (w : DarbouxState) :
    qFirstXX (qFirstBundle g w) = stateQDenominator g w := rfl

theorem qFirstBundle_distance (g h : MetricField) (w : DarbouxState) :
    ‖qFirstBundle g w-qFirstBundle h w‖ =
      ‖actualCurvatureFirstInput g (statePoint w)-actualCurvatureFirstInput h (statePoint w)‖ := by
  simp [qFirstBundle,Prod.norm_def]

theorem qFirstConnection_contDiffAt {a : QFirstInput} (ha : a ∈ qFirstBase)
    (i j : Fin 2) : ContDiffAt ℝ ∞ (fun b => qFirstConnection b i j) a := by
  have hΓ (k : Fin 2) : ContDiffAt ℝ ∞
      (fun b : QFirstInput => christoffelJet (Matrix.of b.1.1) b.1.2 k i j) a :=
    christoffelJet_contDiffAt (G := fun b : QFirstInput => Matrix.of b.1.1)
      (D := fun b : QFirstInput => b.1.2) (fun row column => by
        simp only [Matrix.of_apply]
        fun_prop)
      (fun d i j => by fun_prop) ha k i j
  have hv (k : Fin 2) : ContDiffAt ℝ ∞
      (fun b : QFirstInput => stateGradient b.2 k) a :=
    ((contDiff_apply ℝ ℝ k).comp (stateGradient_contDiff.comp (by fun_prop))).contDiffAt
  simpa only [qFirstConnection,Fin.sum_univ_two] using
    ((hΓ 0).mul (hv 0)).add ((hΓ 1).mul (hv 1))

theorem qFirstXX_contDiffOn : ContDiffOn ℝ ∞ qFirstXX qFirstBase := by
  intro a ha
  exact ((show ContDiffAt ℝ ∞ (fun b : QFirstInput => b.2 5) a by fun_prop).sub
    (qFirstConnection_contDiffAt ha 0 0)).contDiffWithinAt

theorem qFirstDomain_isOpen : IsOpen qFirstDomain :=
  qFirstXX_contDiffOn.continuousOn.isOpen_inter_preimage qFirstBase_isOpen
    isClosed_singleton.isOpen_compl

theorem qFirstEnergy_contDiff : ContDiff ℝ ∞ qFirstEnergy := by
  unfold qFirstEnergy
  have hv (k : Fin 2) : ContDiff ℝ ∞ (fun a : QFirstInput => stateGradient a.2 k) :=
    (contDiff_apply ℝ ℝ k).comp (stateGradient_contDiff.comp (by fun_prop))
  exact qFirstDet_contDiff.sub
    ((((show ContDiff ℝ ∞ (fun a : QFirstInput => a.1.1 1 1) by fun_prop).mul
      ((hv 0).pow 2)).sub
      ((((show ContDiff ℝ ∞ (fun a : QFirstInput => a.1.1 0 1) by fun_prop).add
        (show ContDiff ℝ ∞ (fun a : QFirstInput => a.1.1 1 0) by fun_prop)).mul
          (hv 0)).mul (hv 1))).add
        ((show ContDiff ℝ ∞ (fun a : QFirstInput => a.1.1 0 0) by fun_prop).mul
          ((hv 1).pow 2)))

theorem qFirstDensityFactor_contDiffOn :
    ContDiffOn ℝ ∞ qFirstDensityFactor qFirstDomain := by
  intro a ha
  have hx := qFirstXX_contDiffOn.contDiffAt (qFirstBase_isOpen.mem_nhds ha.1)
  exact (qFirstEnergy_contDiff.contDiffAt.div
    (qFirstDet_contDiff.contDiffAt.mul hx) (mul_ne_zero ha.1 ha.2)).contDiffWithinAt

theorem qFirstLower_contDiffOn : ContDiffOn ℝ ∞ qFirstLower qFirstDomain := by
  intro a ha
  have hΓ := qFirstConnection_contDiffAt ha.1
  have hx := qFirstXX_contDiffOn.contDiffAt (qFirstBase_isOpen.mem_nhds ha.1)
  have hm : ContDiffAt ℝ ∞ qFirstMixed a :=
    (show ContDiffAt ℝ ∞ (fun b : QFirstInput => b.2 4) a by fun_prop).sub (hΓ 0 1)
  exact ((hΓ 1 1).add ((hm.pow 2).div hx ha.2)).contDiffWithinAt

theorem qFirstTube_isCompact (M : ℝ) {d : ℝ} (hd : 0 < d) (c : ℝ) :
    IsCompact (qFirstTube M d c) := by
  have hbase := qFirstBaseTube_isCompact M d
  have hc : ContinuousOn qFirstXX (qFirstBaseTube M d) :=
    qFirstXX_contDiffOn.continuousOn.mono (qFirstBaseTube_subset_base M hd)
  have hclosed : IsClosed (qFirstTube M d c) :=
    hc.preimage_isClosed_of_isClosed hbase.isClosed (isClosed_le continuous_const continuous_abs)
  exact hbase.of_isClosed_subset hclosed inter_subset_left

theorem qFirstXX_fderiv_bound (M : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ qFirstBaseTube M d, ‖fderiv ℝ qFirstXX a‖ ≤ C := by
  have hcont : ContinuousOn (fderiv ℝ qFirstXX) qFirstBase :=
    (qFirstXX_contDiffOn.fderiv_of_isOpen (m := 0) qFirstBase_isOpen (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousOn
  obtain ⟨C,hC⟩ := (qFirstBaseTube_isCompact M d).exists_bound_of_continuousOn
    (hcont.mono (qFirstBaseTube_subset_base M hd))
  exact ⟨max C 0,le_max_right _ _,fun a ha => (hC a ha).trans (le_max_left _ _)⟩

theorem qFirstTube_fderiv_bound (f : QFirstInput → ℝ)
    (hf : ContDiffOn ℝ ∞ f qFirstDomain) (M : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ qFirstTube M d c, ‖fderiv ℝ f a‖ ≤ C := by
  have hcont : ContinuousOn (fderiv ℝ f) qFirstDomain :=
    (hf.fderiv_of_isOpen (m := 0) qFirstDomain_isOpen (by simp)).continuousOn
  obtain ⟨C,hC⟩ := (qFirstTube_isCompact M hd c).exists_bound_of_continuousOn
    (hcont.mono (qFirstTube_subset_domain M hd hc))
  exact ⟨max C 0,le_max_right _ _,fun a ha => (hC a ha).trans (le_max_left _ _)⟩

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_QFirstJetComparison
attribute [-simp] _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero
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

theorem qFirst_segment_distance_le (a b : QFirstInput) {x : QFirstInput}
    (hx : x ∈ segment ℝ a b) : ‖x-a‖ ≤ ‖b-a‖ := by
  have hball : x ∈ Metric.closedBall a ‖b-a‖ :=
    (convex_closedBall a ‖b-a‖).segment_subset
      (by simp) (by simp only [Metric.mem_closedBall,dist_eq_norm,le_refl]) hx
  simpa only [Metric.mem_closedBall,dist_eq_norm] using hball

theorem qFirst_close_segment_subset_baseTube (a b : QFirstInput) {B d : ℝ}
    (ha : ‖a‖ ≤ B) (hdet : d ≤ qFirstDet a) (hdist : ‖b-a‖ ≤ 1)
    (hsmall : (4*max B 0+2)*‖b-a‖ ≤ d/2) :
    segment ℝ a b ⊆ qFirstBaseTube (max B 0+1) (d/2) := by
  intro x hx
  have hxa := qFirst_segment_distance_le a b hx
  have hxnorm : ‖x‖ ≤ max B 0+1 := by
    calc
      _ = ‖(x-a)+a‖ := by rw [sub_add_cancel]
      _ ≤ ‖x-a‖+‖a‖ := norm_add_le _ _
      _ ≤ 1+max B 0 := add_le_add (hxa.trans hdist) (ha.trans (le_max_left _ _))
      _ = _ := by ring
  have hmatrixD : ‖x.1.1-a.1.1‖ ≤ ‖b-a‖ :=
    (show ‖x.1.1-a.1.1‖ ≤ ‖x-a‖ from
      (norm_fst_le (x-a).1).trans (norm_fst_le (x-a))).trans hxa
  have hmatrixA : ‖a.1.1‖ ≤ max B 0 :=
    ((norm_fst_le a.1).trans (norm_fst_le a)).trans (ha.trans (le_max_left _ _))
  have hdetdiff := det_sub_le_small_first_distance (Matrix.of a.1.1) (Matrix.of x.1.1)
    (le_max_right B 0) (norm_nonneg _) hdist hmatrixA hmatrixD
  have hxdet : d/2 ≤ qFirstDet x := by
    have hneg := neg_abs_le (qFirstDet x-qFirstDet a)
    change |qFirstDet x-qFirstDet a| ≤ (4*max B 0+2)*‖b-a‖ at hdetdiff
    linarith [hdetdiff.trans hsmall]
  exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxnorm,hxdet⟩

theorem exists_uniform_qFirst_comparison (B : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) :
    ∃ H F L : ℝ, 0 ≤ H ∧ 0 ≤ F ∧ 0 ≤ L ∧
      ∀ a b : QFirstInput, ‖a‖ ≤ B → d ≤ qFirstDet a → c ≤ |qFirstXX a| →
        ‖b-a‖ ≤ 1 → (4*max B 0+2)*‖b-a‖ ≤ d/2 → H*‖b-a‖ ≤ c/2 →
        (∀ x ∈ segment ℝ a b, c/2 ≤ |qFirstXX x|) ∧
        |qFirstDensityFactor b-qFirstDensityFactor a| ≤ F*‖b-a‖ ∧
        |qFirstLower b-qFirstLower a| ≤ L*‖b-a‖ := by
  obtain ⟨H,hH,hHb⟩ := qFirstXX_fderiv_bound (max B 0+1) (half_pos hd)
  obtain ⟨F,hF,hFb⟩ := qFirstTube_fderiv_bound qFirstDensityFactor
    qFirstDensityFactor_contDiffOn (max B 0+1) (half_pos hd) (half_pos hc)
  obtain ⟨L,hL,hLb⟩ := qFirstTube_fderiv_bound qFirstLower
    qFirstLower_contDiffOn (max B 0+1) (half_pos hd) (half_pos hc)
  refine ⟨H,F,L,hH,hF,hL,?_⟩
  intro a b ha hdet hxx hdist hsmall hxxsmall
  have hbase := qFirst_close_segment_subset_baseTube a b ha hdet hdist hsmall
  have hXXdiff : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ qFirstXX x := by
    intro x hx
    exact (qFirstXX_contDiffOn.contDiffAt (qFirstBase_isOpen.mem_nhds
      (qFirstBaseTube_subset_base (max B 0+1) (half_pos hd) (hbase hx)))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hfloor : ∀ x ∈ segment ℝ a b, c/2 ≤ |qFirstXX x| := by
    intro x hx
    have herr : |qFirstXX x-qFirstXX a| ≤ H*‖x-a‖ := by
      simpa only [Real.norm_eq_abs] using
        (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le hXXdiff
          (fun y hy => hHb y (hbase hy)) (left_mem_segment ℝ a b) hx
    have hsmall' : |qFirstXX x-qFirstXX a| ≤ c/2 :=
      herr.trans ((mul_le_mul_of_nonneg_left (qFirst_segment_distance_le a b hx) hH).trans hxxsmall)
    have htriangle : |qFirstXX a| ≤ |qFirstXX x|+|qFirstXX x-qFirstXX a| := by
      calc
        _ = |qFirstXX x-(qFirstXX x-qFirstXX a)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    linarith
  have htube : segment ℝ a b ⊆ qFirstTube (max B 0+1) (d/2) (c/2) :=
    fun x hx => ⟨hbase hx,hfloor x hx⟩
  have hcompare (f : QFirstInput → ℝ) (hf : ContDiffOn ℝ ∞ f qFirstDomain)
      (C : ℝ) (hCb : ∀ x ∈ qFirstTube (max B 0+1) (d/2) (c/2), ‖fderiv ℝ f x‖ ≤ C) :
      |f b-f a| ≤ C*‖b-a‖ := by
    have hdiff : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ f x := by
      intro x hx
      exact (hf.contDiffAt (qFirstDomain_isOpen.mem_nhds
        (qFirstTube_subset_domain (max B 0+1) (half_pos hd) (half_pos hc)
          (htube hx)))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [Real.norm_eq_abs] using
      (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le hdiff
        (fun x hx => hCb x (htube hx)) (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  exact ⟨hfloor,hcompare _ qFirstDensityFactor_contDiffOn F hFb,
    hcompare _ qFirstLower_contDiffOn L hLb⟩

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_ActualShearHeight
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem covHessian_in_shear_coordinates {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U) :
    covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p =
      (inverseShearMatrix q0)ᵀ * covHessian g z (inverseShearCoordinates q0 p) *
        inverseShearMatrix q0 := by
  simpa only [metricInShearCoordinates, heightInShearCoordinates,
    inverseShearCoordinates_eq_affine] using
    covHessian_affinePullback hg hz hU 0 (inverseShearMatrix q0)
      (inverseShearMatrix_isUnit q0) p (by simpa only [← inverseShearCoordinates_eq_affine] using hp)

theorem heightEnergy_in_shear_coordinates {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U) :
    heightEnergy (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p =
      heightEnergy g z (inverseShearCoordinates q0 p) := by
  have hd := (hz.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  simpa only [metricInShearCoordinates, heightInShearCoordinates,
    ← inverseShearCoordinates_eq_affine, inverseShearMatrix_det, one_pow, one_mul] using
    heightEnergy_affinePullback (g := g) 0 (inverseShearMatrix q0)
      (inverseShearMatrix_isUnit q0) p
      (by simpa only [← inverseShearCoordinates_eq_affine] using hd)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ActualQPulseForcing
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

theorem curvatureDensity_in_shear_coordinates {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (q0 : ℝ) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U) :
    curvatureDensity (metricInShearCoordinates g q0) p =
      curvatureDensity g (inverseShearCoordinates q0 p) := by
  have hpa : affineCoordinates 0 (inverseShearMatrix q0) p ∈ U := by
    simpa only [←inverseShearCoordinates_eq_affine] using hp
  unfold curvatureDensity metricInShearCoordinates
  rw [gaussianCurvature_affinePullback hg hU 0 (inverseShearMatrix q0)
    (inverseShearMatrix_isUnit q0) p hpa,det_affinePullbackMetric]
  simp only [inverseShearMatrix_det,one_pow,one_mul,←inverseShearCoordinates_eq_affine]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ShearFirstJetComparison
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

theorem actualCurvatureFirstInput_affinePullback {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (b : Coord) (R : MetricMatrix)
    (p : Coord) (hp : affineCoordinates b R p ∈ U) :
    actualCurvatureFirstInput (affinePullbackMetric g b R) p =
      affineFirstJetMap R (actualCurvatureFirstInput g (affineCoordinates b R p)) := by
  apply Prod.ext
  · funext i j
    simp only [actualCurvatureFirstInput,affineFirstJetMap,affinePullbackMetric,
      Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]
    ring
  · funext k i j
    exact coordPartial_affinePullbackMetric hg hU b R p hp k i j

theorem actual_shear_first_jet_distance_le {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {q0 e : ℝ} (hq : |q0| ≤ 1) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hjet : ‖actualCurvatureFirstInput g (inverseShearCoordinates q0 p)-
      actualCurvatureFirstInput h (inverseShearCoordinates q0 p)‖ ≤ e) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates g q0) p-
      actualCurvatureFirstInput (metricInShearCoordinates h q0) p‖ ≤ 8*e := by
  have he : 0 ≤ e := (norm_nonneg _).trans hjet
  have hp' : affineCoordinates 0 (inverseShearMatrix q0) p ∈ U := by
    simpa only [←inverseShearCoordinates_eq_affine] using hp
  unfold metricInShearCoordinates
  rw [actualCurvatureFirstInput_affinePullback hg hU 0 (inverseShearMatrix q0) p hp',
    actualCurvatureFirstInput_affinePullback hh hU 0 (inverseShearMatrix q0) p hp',
    ←affineFirstJetMap_sub]
  exact affineFirstJetMap_norm_le_eight _ (inverseShearMatrix_entry_le_one hq) _ he
    (by simpa only [←inverseShearCoordinates_eq_affine] using hjet)

theorem actualCurvatureFirstInput_thetaPulseMetric {g : MetricField} {f : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    actualCurvatureFirstInput (thetaPulseMetric g f) p =
      actualCurvatureFirstInput g p+thetaCurvatureFirstIncrement f p := by
  apply Prod.ext
  · rfl
  · exact metricFirstJet_thetaPulseMetric hg hf hU hp

theorem actual_sheared_solution_first_jet_error
    {gStar gTau : MetricField} {U : Set Coord} {q0 a delta tau e : ℝ} {N : ℕ}
    (hgStar : SmoothPositiveOn gStar U)
    (hgTest : SmoothPositiveOn (testMetric gStar q0 a N delta tau) U)
    (hgTau : SmoothPositiveOn gTau U) (hU : IsOpen U)
    (hq : |q0| ≤ 1) (ha : 0 < a) (ht : 1 ≤ tau) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U)
    (hjet : ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
      actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
        (inverseShearCoordinates q0 p)‖ ≤ e) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
      actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤
      8*e+scalarPulseFirstJetBudget a ha N delta tau := by
  have hcomp := actual_shear_first_jet_distance_le hgTau hgTest hU hq hp hjet
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hpV : p ∈ V := hp
  have hgV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hgStar 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have heq : actualCurvatureFirstInput
      (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) p-
        actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p =
      thetaCurvatureFirstIncrement (pulseScalar a N delta tau) p := by
    rw [metricInShearCoordinates_test,
      actualCurvatureFirstInput_thetaPulseMetric hgV (pulseScalar_contDiff a N delta tau).contDiffOn hV hpV]
    exact add_sub_cancel_left _ _
  calc
    _ ≤ ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
        actualCurvatureFirstInput (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) p‖+
        ‖actualCurvatureFirstInput (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) p-
          actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p)
        (actualCurvatureFirstInput (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) p)
        (actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p)
    _ ≤ _ := add_le_add hcomp (by rw [heq]; exact thetaPulse_first_increment_bound ha N delta ht p)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_ShearHeightJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem sheared_full_jet_bound_of_coordinateBound {z : Coord → ℝ} {U S : Set Coord}
    {N n : ℕ} {B : ℝ} (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hSU : S ⊆ U) (hbound : CoordinateBound z S N B) (hB : 0 ≤ B)
    (q0 : ℝ) (hn : n ≤ N) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ S) :
    ‖iteratedFDeriv ℝ n (heightInShearCoordinates z q0) p‖ ≤
      (2 * (1 + |q0|))^N * B := by
  have hlocal := local_linear_full_jet_norm_bound hz hU (inverseShearCLM q0) (hSU hp) n
  have hbase := hbound.full_jet_norm_bound hz hU hSU hB hn hp
  have hscale : 1 ≤ 2 * (1 + |q0|) := by nlinarith [abs_nonneg q0]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n z (inverseShearCoordinates q0 p)‖ * ‖inverseShearCLM q0‖^n := hlocal
    _ ≤ ((2 : ℝ)^n * B) * (1 + |q0|)^n := mul_le_mul hbase
      (pow_le_pow_left₀ (norm_nonneg _) (inverseShearCLM_norm_le q0) n)
      (pow_nonneg (norm_nonneg _) n) (mul_nonneg (by positivity) hB)
    _ = (2 * (1 + |q0|))^n * B := by rw [mul_pow]; ring
    _ ≤ (2 * (1 + |q0|))^N * B :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hscale hn) hB

theorem CoordinateBound.inverse_shear {z : Coord → ℝ} {U S : Set Coord}
    {N : ℕ} {B : ℝ} (hbound : CoordinateBound z S N B)
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (hSU : S ⊆ U) (hB : 0 ≤ B) (q0 : ℝ) :
    CoordinateBound (heightInShearCoordinates z q0) (inverseShearCoordinates q0 ⁻¹' S)
      N ((2 * (1 + |q0|))^N * B) := by
  intro ds hds p hp
  apply (norm_iteratedCoordPartial_le_jet (heightInShearCoordinates_contDiffOn hz q0)
    (hU.preimage (inverseShearCoordinates_contDiff q0).continuous) ds (hSU hp)).trans
  exact sheared_full_jet_bound_of_coordinateBound hz hU hSU hbound hB q0 hds hp

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_ActualShearHyperbolicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem metricInShearCoordinates_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (q0 : ℝ) :
    SmoothPositiveOn (metricInShearCoordinates g q0) (inverseShearCoordinates q0 ⁻¹' U) := by
  simpa only [metricInShearCoordinates, inverseShearCoordinates_eq_affine] using
    affinePullbackMetric_smoothPositive hg 0 (inverseShearMatrix q0)
      (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))

theorem gaussianCurvature_in_shear_coordinates {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (q0 : ℝ) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U) :
    gaussianCurvature (metricInShearCoordinates g q0) p =
      gaussianCurvature g (inverseShearCoordinates q0 p) := by
  simpa only [metricInShearCoordinates, ← inverseShearCoordinates_eq_affine] using
    gaussianCurvature_affinePullback hg hU 0 (inverseShearMatrix q0)
      (inverseShearMatrix_isUnit q0) p
      (by simpa only [← inverseShearCoordinates_eq_affine] using hp)

theorem darboux_in_shear_coordinates {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hD : (covHessian g z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature g (inverseShearCoordinates q0 p) *
        heightEnergy g z (inverseShearCoordinates q0 p)) :
    (covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p).det =
      gaussianCurvature (metricInShearCoordinates g q0) p *
        heightEnergy (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p := by
  rw [covHessian_in_shear_coordinates hg hz hU q0 hp,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, inverseShearMatrix_det,
    one_mul, mul_one, hD, gaussianCurvature_in_shear_coordinates hg hU q0 hp,
    heightEnergy_in_shear_coordinates hz hU q0 hp]

def shearTimeFactor (g : MetricField) (z : Coord → ℝ) (q0 : ℝ) (p : Coord) : ℝ :=
  (hessianQuotient g z (inverseShearCoordinates q0 p) - q0) ^ 2 +
    gaussianCurvature g (inverseShearCoordinates q0 p) *
      darbouxG g z (inverseShearCoordinates q0 p)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_ShearMetricJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem metricDet_in_shear_coordinates (g : MetricField) (q0 : ℝ) (p : Coord) :
    (metricInShearCoordinates g q0 p).det = (g (inverseShearCoordinates q0 p)).det := by
  simp only [metricInShearCoordinates, det_affinePullbackMetric,
    inverseShearMatrix_det, one_pow, one_mul, ← inverseShearCoordinates_eq_affine]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_HyperbolicEnergyDensity
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted

variable {P S bTheta bXi v R : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem energy_density_flux_identity
    (hP : DifferentiableAt ℝ P p) (hS : DifferentiableAt ℝ S p)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hp : p ∈ U)
    (hEq : hyperbolicOperator P S v p =
      bTheta p * coordPartial 1 v p + bXi p * coordPartial 0 v p + R p) :
    coordPartial 1 (energyDensity S v) p - coordPartial 0 (energyFlux P S v) p =
      energyCoefficientError P S bTheta bXi v p + R p * coordPartial 1 v p := by
  have hd (i : Fin 2) : DifferentiableAt ℝ (coordPartial i v) p :=
    ((partial_contDiffOn hv hU i).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [energyDensity_partial_theta hS (hd 1) (hd 0),
    energyFlux_partial_xi hP hS (hd 1) (hd 0), coordPartial_comm hv hU hp 1 0]
  unfold hyperbolicOperator at hEq
  unfold energyCoefficientError
  nlinarith [congrArg (fun x : ℝ => x * coordPartial 1 v p) hEq]

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_MovingIntervalCalculus
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem slice_intervalIntegrable
    {f : Coord → ℝ} {radius lo hi xl xr theta : ℝ}
    (hf : ContinuousOn f (coordinateRectangle radius lo hi))
    (hxl : xl ∈ Ioo (-radius) radius) (hxr : xr ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    IntervalIntegrable (fun xi => f (coordinatePoint xi theta)) volume xl xr := by
  have hc : ContinuousOn (fun xi => f (coordinatePoint xi theta)) (Ioo (-radius) radius) :=
    hf.comp (by unfold coordinatePoint; fun_prop) (fun xi hxi => point_mem_rectangle hxi htheta)
  exact (hc.mono (fun xi hxi =>
    ⟨lt_of_lt_of_le (lt_min hxl.1 hxr.1) hxi.1,
      lt_of_le_of_lt hxi.2 (max_lt hxl.2 hxr.2)⟩)).intervalIntegrable

theorem movingIntervalIntegral_eq_primitive
    {f : Coord → ℝ} {left right : ℝ → ℝ} {radius lo hi theta : ℝ}
    (hf : ContinuousOn f (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hl : left theta ∈ Ioo (-radius) radius) (hr : right theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    movingIntervalIntegral left right f theta =
      coordinatePrimitive f (coordinatePoint (right theta) theta) -
      coordinatePrimitive f (coordinatePoint (left theta) theta) := by
  have h0 : (0 : ℝ) ∈ Ioo (-radius) radius := ⟨by linarith, hradius⟩
  have hrI := slice_intervalIntegrable hf h0 hr htheta
  have hlI := slice_intervalIntegrable hf h0 hl htheta
  simpa [movingIntervalIntegral, coordinatePrimitive, coordinatePoint] using
    (intervalIntegral.integral_interval_sub_left hrI hlI).symm

theorem slice_integral_partial_xi
    {f : Coord → ℝ} {radius lo hi xl xr theta : ℝ}
    (hf : ContDiffOn ℝ ∞ f (coordinateRectangle radius lo hi))
    (hxl : xl ∈ Ioo (-radius) radius) (hxr : xr ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    (∫ xi in xl..xr, coordPartial 0 f (coordinatePoint xi theta)) =
      f (coordinatePoint xr theta) - f (coordinatePoint xl theta) := by
  have hmem {xi : ℝ} (hxi : xi ∈ uIcc xl xr) :
      coordinatePoint xi theta ∈ coordinateRectangle radius lo hi :=
    point_mem_rectangle
      ⟨lt_of_lt_of_le (lt_min hxl.1 hxr.1) hxi.1,
        lt_of_le_of_lt hxi.2 (max_lt hxl.2 hxr.2)⟩ htheta
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro xi hxi
    have hd : DifferentiableAt ℝ f (coordinatePoint xi theta) :=
      (hf.contDiffAt ((coordinateRectangle_isOpen radius lo hi).mem_nhds
        (hmem hxi))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact hd.hasFDerivAt.comp_hasDerivAt xi (point_hasDerivAt_t xi theta)
  · exact slice_intervalIntegrable
      (partial_contDiffOn hf (coordinateRectangle_isOpen radius lo hi) 0).continuousOn
      hxl hxr htheta

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MovingSlabEnergy
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

variable {P S bTheta bXi v R : Coord → ℝ} {radius lo hi xl xr theta0 speed theta : ℝ}

theorem moving_source_integral_bound_of_slicePositivity
    (hS : ContDiffOn ℝ ∞ S (coordinateRectangle radius lo hi))
    (hv : ContDiffOn ℝ ∞ v (coordinateRectangle radius lo hi))
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi))
    (hl : inwardLeft xl theta0 speed theta ∈ Ioo (-radius) radius)
    (hr : inwardRight xr theta0 speed theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi)
    (hlr : inwardLeft xl theta0 speed theta ≤ inwardRight xr theta0 speed theta)
    (hSpos : ∀ x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta),
      0 ≤ S (coordinatePoint x theta)) :
    movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
      (fun p => R p * coordPartial 1 v p) theta ≤
      Real.sqrt (2 * movingEnergy xl xr theta0 speed S v theta) *
        movingSourceNorm xl xr theta0 speed R theta := by
  let l := inwardLeft xl theta0 speed theta
  let r := inwardRight xr theta0 speed theta
  let U := coordinateRectangle radius lo hi
  have hU : IsOpen U := coordinateRectangle_isOpen radius lo hi
  have hmem {x : ℝ} (hx : x ∈ Icc l r) : coordinatePoint x theta ∈ U :=
    point_mem_rectangle ⟨hl.1.trans_le hx.1, hx.2.trans_lt hr.2⟩ htheta
  have hvt := partial_contDiffOn hv hU 1
  have hx := partial_contDiffOn hv hU 0
  have he : ContDiffOn ℝ ∞ (energyDensity S v) U :=
    ((hvt.pow 2).add (hS.mul (hx.pow 2))).div_const 2
  have he2 : ContDiffOn ℝ ∞ (fun p => 2 * energyDensity S v p) U :=
    contDiffOn_const.mul he
  have hcR : ContinuousOn (fun x => R (coordinatePoint x theta)) (Icc l r) :=
    hR.continuousOn.comp (by unfold coordinatePoint; fun_prop) (fun x hx => hmem hx)
  have hcvt : ContinuousOn (fun x => coordPartial 1 v (coordinatePoint x theta)) (Icc l r) :=
    hvt.continuousOn.comp (by unfold coordinatePoint; fun_prop) (fun x hx => hmem hx)
  have hC := interval_product_abs_le_sqrt_squares hlr hcR hcvt
  have hkin : (∫ x in l..r, (coordPartial 1 v (coordinatePoint x theta)) ^ 2) ≤
      2 * movingEnergy xl xr theta0 speed S v theta := by
    have hI := intervalIntegral.integral_mono_on hlr
      (slice_intervalIntegrable (hvt.pow 2).continuousOn hl hr htheta)
      (slice_intervalIntegrable he2.continuousOn hl hr htheta)
      (fun x hx => by
        have hs := hSpos x hx
        unfold energyDensity
        nlinarith [mul_nonneg hs (sq_nonneg (coordPartial 0 v (coordinatePoint x theta)))])
    simpa only [movingEnergy, movingIntervalIntegral, intervalIntegral.integral_const_mul] using hI
  have hroot := Real.sqrt_le_sqrt hkin
  have hmul := mul_le_mul_of_nonneg_left hroot
    (Real.sqrt_nonneg (∫ x in l..r, R (coordinatePoint x theta) ^ 2))
  unfold movingIntervalIntegral movingSourceNorm
  exact (le_abs_self _).trans (hC.trans
    (by simpa only [l, r, movingIntervalIntegral, mul_comm] using hmul))

theorem movingEnergyRate_le_of_sliceBounds
    (hP : ContDiffOn ℝ ∞ P (coordinateRectangle radius lo hi))
    (hS : ContDiffOn ℝ ∞ S (coordinateRectangle radius lo hi))
    (hbt : ContDiffOn ℝ ∞ bTheta (coordinateRectangle radius lo hi))
    (hbx : ContDiffOn ℝ ∞ bXi (coordinateRectangle radius lo hi))
    (hv : ContDiffOn ℝ ∞ v (coordinateRectangle radius lo hi))
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi))
    (hl : inwardLeft xl theta0 speed theta ∈ Ioo (-radius) radius)
    (hr : inwardRight xr theta0 speed theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi)
    (hlr : inwardLeft xl theta0 speed theta ≤ inwardRight xr theta0 speed theta)
    {s0 M : ℝ} (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hSfloor : ∀ x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta),
      s0 ≤ S (coordinatePoint x theta))
    (hcoeff : ∀ x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta),
      |bTheta (coordinatePoint x theta)| ≤ M ∧ |bXi (coordinatePoint x theta)| ≤ M ∧
      |coordPartial 0 P (coordinatePoint x theta)| ≤ M ∧
      |coordPartial 0 S (coordinatePoint x theta)| ≤ M ∧
      |coordPartial 1 S (coordinatePoint x theta)| ≤ M)
    (hspeed : ∀ x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta),
      |P (coordinatePoint x theta)| + Real.sqrt (S (coordinatePoint x theta)) ≤ speed) :
    movingEnergyRate xl xr theta0 speed P S bTheta bXi v R theta ≤
      (8 * M * (1 + 1 / s0)) * movingEnergy xl xr theta0 speed S v theta +
      Real.sqrt (2 * movingEnergy xl xr theta0 speed S v theta) *
        movingSourceNorm xl xr theta0 speed R theta := by
  let U := coordinateRectangle radius lo hi
  have hU : IsOpen U := coordinateRectangle_isOpen radius lo hi
  obtain ⟨he, hj, herr⟩ := energy_fields_contDiffOn hU hP hS hbt hbx hv
  have heC : ContDiffOn ℝ ∞
      (fun p => (8 * M * (1 + 1 / s0)) * energyDensity S v p) U :=
    contDiffOn_const.mul he
  have hsource := hR.mul (partial_contDiffOn hv hU 1)
  have hmem {x : ℝ}
      (hx : x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta)) :
      coordinatePoint x theta ∈ U :=
    point_mem_rectangle ⟨hl.1.trans_le hx.1, hx.2.trans_lt hr.2⟩ htheta
  have hSl := hSfloor _ ⟨le_rfl, hlr⟩
  have hSr := hSfloor _ ⟨hlr, le_rfl⟩
  have hboundary := inward_boundary_nonpositive (v := v) (hs0.le.trans hSl) (hs0.le.trans hSr)
    (hspeed _ ⟨le_rfl, hlr⟩) (hspeed _ ⟨hlr, le_rfl⟩)
  have herrI : movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
      (energyCoefficientError P S bTheta bXi v) theta ≤
      (8 * M * (1 + 1 / s0)) * movingEnergy xl xr theta0 speed S v theta := by
    have hh := intervalIntegral.integral_mono_on hlr
      (slice_intervalIntegrable herr.continuousOn hl hr htheta)
      (slice_intervalIntegrable heC.continuousOn hl hr htheta)
      (fun x hx => by
        obtain ⟨hbt', hbx', hPx', hSx', hSt'⟩ := hcoeff x hx
        exact (le_abs_self _).trans (energyCoefficientError_abs_le hs0
          (hSfloor x hx) hM hbt' hbx' hPx' hSx' hSt'))
    simpa only [movingIntervalIntegral, movingEnergy, intervalIntegral.integral_const_mul] using hh
  have hsourceI := moving_source_integral_bound_of_slicePositivity hS hv hR hl hr htheta hlr
    (fun p hp => hs0.le.trans (hSfloor p hp))
  unfold movingEnergyRate movingIntervalIntegral
  rw [intervalIntegral.integral_add
    (slice_intervalIntegrable herr.continuousOn hl hr htheta)
    (slice_intervalIntegrable hsource.continuousOn hl hr htheta)]
  dsimp only [movingIntervalIntegral] at herrI hsourceI
  linarith

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MovingIntervalSobolev
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal NNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Sobolev

theorem spatialJet_slice_hasDerivAt
    {f : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) {x theta : ℝ} (hp : coordinatePoint x theta ∈ U) :
    HasDerivAt (fun xi => spatialJet f n (coordinatePoint xi theta))
      (spatialJet f (n + 1) (coordinatePoint x theta)) x := by
  have hd := ((spatialJet_contDiffOn hU hf n).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact hd.hasFDerivAt.comp_hasDerivAt x (point_hasDerivAt_t x theta)

theorem spatialJet_point_bound_from_same_interval_L2
    {f : Coord → ℝ} {U : Set Coord} {left right theta lengthFloor : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (n : ℕ) {H : ℝ≥0}
    (h0 : eLpNorm (fun x => spatialJet f n (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞))
    (h1 : eLpNorm (fun x => spatialJet f (n + 1) (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞))
    {x : ℝ} (hx : x ∈ Icc left right) :
    |spatialJet f n (coordinatePoint x theta)| ≤
      Real.sqrt (2 + 1 / lengthFloor) * (H : ℝ) := by
  have hlr : left < right := by linarith
  have hc0 : ContinuousOn (fun x => spatialJet f n (coordinatePoint x theta)) (Icc left right) :=
    (spatialJet_contDiffOn hU hf n).continuousOn.comp
      (by unfold coordinatePoint; fun_prop) hseg
  have hc1 : ContinuousOn (fun x => spatialJet f (n + 1) (coordinatePoint x theta))
      (Icc left right) :=
    (spatialJet_contDiffOn hU hf (n + 1)).continuousOn.comp
      (by unfold coordinatePoint; fun_prop) hseg
  have hp := interval_point_square_bound hlr hc0 hc1
    (fun x hx => spatialJet_slice_hasDerivAt hU hf n (hseg x hx)) hx
  have h0I := interval_square_integral_le_of_eLpNorm hlr.le
    (smooth_slice_memLp_two (spatialJet_contDiffOn hU hf n).continuousOn hseg) h0
  have h1I := interval_square_integral_le_of_eLpNorm hlr.le
    (smooth_slice_memLp_two (spatialJet_contDiffOn hU hf (n + 1)).continuousOn hseg) h1
  have hinv : 1 / (right - left) ≤ 1 / lengthFloor := by
    exact one_div_le_one_div_of_le hlength hwidth
  have hc : 0 ≤ 1 + 1 / (right - left) := by positivity
  have h0scale := mul_le_mul_of_nonneg_left h0I hc
  have hInvScale := mul_le_mul_of_nonneg_right hinv (sq_nonneg (H : ℝ))
  have hpoint : spatialJet f n (coordinatePoint x theta) ^ 2 ≤
      (2 + 1 / lengthFloor) * (H : ℝ) ^ 2 := by nlinarith
  have hpos : 0 ≤ 2 + 1 / lengthFloor := by positivity
  have hroot := Real.sq_sqrt hpos
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) H.2)).1
  rw [sq_abs, mul_pow, hroot]
  exact hpoint

theorem SpatialSliceL2Bound.pointwise_below_top
    {ι : Type*} {F : ι → Coord → ℝ} {U : Set Coord}
    {theta left right lengthFloor : ℝ} {N : ℕ} {H : ℝ≥0}
    (hL2 : SpatialSliceL2Bound F theta left right N H)
    (hU : IsOpen U) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (i : ι) (n : ℕ) (hn : n + 1 ≤ N) {x : ℝ} (hx : x ∈ Icc left right) :
    |spatialJet (F i) n (coordinatePoint x theta)| ≤
      Real.sqrt (2 + 1 / lengthFloor) * (H : ℝ) :=
  spatialJet_point_bound_from_same_interval_L2 hU (hF i) hseg hlength hwidth n
    (hL2 i n (by omega)) (hL2 i (n + 1) hn) hx

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_HorizontalJetCalculus
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem horizontalJet_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∀ n, ContDiffOn ℝ ∞ (horizontalJet f n) U := by
  intro n
  induction n with
  | zero => exact hf
  | succ _ hn => exact normed_coordPartial_contDiffOn hn hU 0

theorem horizontalJet_slice_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (n : ℕ)
    (hp : coordinatePoint x y ∈ U) :
    HasDerivAt (fun t => horizontalJet f n (coordinatePoint t y))
      (horizontalJet f (n + 1) (coordinatePoint x y)) x := by
  have hd : DifferentiableAt ℝ (horizontalJet f n) (coordinatePoint x y) :=
    ((horizontalJet_contDiffOn hU hf n).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact hd.hasFDerivAt.comp_hasDerivAt x (point_hasDerivAt_t x y)

theorem horizontalJet_slice
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (y : ℝ) : ∀ n x, coordinatePoint x y ∈ U →
      iteratedDeriv n (fun t => f (coordinatePoint t y)) x =
        horizontalJet f n (coordinatePoint x y) := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n hn =>
    intro x hx
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun t => f (coordinatePoint t y)) =ᶠ[𝓝 x]
        (fun t => horizontalJet f n (coordinatePoint t y)) := by
      filter_upwards [(hU.preimage (horizontalPoint_contDiff y).continuous).mem_nhds hx] with t ht
      exact hn t ht
    rw [heq.deriv_eq]
    exact (horizontalJet_slice_hasDerivAt hU hf n hx).deriv

theorem horizontalJet_coordPartial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (i : Fin 2) : ∀ n p, p ∈ U →
      horizontalJet (coordPartial i f) n p = coordPartial i (horizontalJet f n) p := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n hn =>
    intro p hp
    have heq : horizontalJet (coordPartial i f) n =ᶠ[𝓝 p] coordPartial i (horizontalJet f n) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hn q hq
    have hd : coordPartial 0 (horizontalJet (coordPartial i f) n) p =
        coordPartial 0 (coordPartial i (horizontalJet f n)) p :=
      congrArg (fun L : Coord →L[ℝ] V => L (Pi.single 0 1)) heq.fderiv_eq
    change coordPartial 0 (horizontalJet (coordPartial i f) n) p =
      coordPartial i (coordPartial 0 (horizontalJet f n)) p
    rw [hd]
    exact coordPartial_comm (horizontalJet_contDiffOn hU hf n) hU hp 0 i

theorem horizontalJet_two_coordPartials
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hp : p ∈ U) (n : ℕ) (i j : Fin 2) :
    horizontalJet (coordPartial i (coordPartial j f)) n p =
      coordPartial i (coordPartial j (horizontalJet f n)) p := by
  rw [horizontalJet_coordPartial hU (normed_coordPartial_contDiffOn hf hU j) i n p hp]
  have heq : horizontalJet (coordPartial j f) n =ᶠ[𝓝 p] coordPartial j (horizontalJet f n) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact horizontalJet_coordPartial hU hf j n q hq
  exact congrArg (fun L : Coord →L[ℝ] V => L (Pi.single i 1)) heq.fderiv_eq

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSpatialJets
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem qSolutionJetCurve_iteratedDeriv_positive
    {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : coordinatePoint x y ∈ U)
    (n : ℕ) (hn : 0 < n) :
    iteratedDeriv n (qSolutionJetCurve z y) x =
      ![if n = 1 then 1 else 0, 0,
        spatialJet (spatialFirstJet z 0) n (coordinatePoint x y),
        spatialJet (spatialFirstJet z 1) n (coordinatePoint x y),
        spatialJet (spatialFirstJet z 1) (n + 1) (coordinatePoint x y),
        spatialJet (spatialFirstJet z 0) (n + 1) (coordinatePoint x y)] := by
  have hc := qSolutionJetCurve_contDiffAt hU hz hp
  ext i
  rw [iteratedDeriv_state_eval hc n i]
  fin_cases i
  · simpa [qSolutionJetCurve, qSolutionJet, coordinatePoint, hn.ne'] using
      (iteratedDeriv_fun_id (n := n) (x := x))
  · simp [qSolutionJetCurve, qSolutionJet, coordinatePoint, iteratedDeriv_const, hn.ne']
  · change iteratedDeriv n (fun t => coordPartial 0 z (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn hz hU 0) y n x hp,
      horizontalJet_eq_spatialJet]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 z (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn hz hU 1) y n x hp,
      horizontalJet_eq_spatialJet]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 1 z) (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0) y n x hp,
      horizontalJet_coordPartial hU (partial_contDiffOn hz hU 1) 0 n _ hp,
      horizontalJet_eq_spatialJet]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 0 z) (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0) y n x hp,
      horizontalJet_coordPartial hU (partial_contDiffOn hz hU 0) 0 n _ hp,
      horizontalJet_eq_spatialJet]
    rfl

theorem qSolutionJetCurve_iteratedDeriv
    {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : coordinatePoint x y ∈ U)
    (n : ℕ) (hn : 2 ≤ n) :
    iteratedDeriv n (qSolutionJetCurve z y) x =
      ![0, 0, coordPartial 0 (horizontalJet z n) (coordinatePoint x y),
        coordPartial 1 (horizontalJet z n) (coordinatePoint x y),
        coordPartial 0 (coordPartial 1 (horizontalJet z n)) (coordinatePoint x y),
        coordPartial 0 (coordPartial 0 (horizontalJet z n)) (coordinatePoint x y)] := by
  have hc := qSolutionJetCurve_contDiffAt hU hz hp
  ext i
  rw [iteratedDeriv_state_eval hc n i]
  fin_cases i
  · simp [qSolutionJetCurve, qSolutionJet, coordinatePoint, iteratedDeriv_fun_id,
      show n ≠ 0 by omega, show n ≠ 1 by omega]
  · simp [qSolutionJetCurve, qSolutionJet, coordinatePoint, iteratedDeriv_const,
      show n ≠ 0 by omega]
  · change iteratedDeriv n (fun t => coordPartial 0 z (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn hz hU 0) y n x hp,
      horizontalJet_coordPartial hU hz 0 n _ hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 z (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn hz hU 1) y n x hp,
      horizontalJet_coordPartial hU hz 1 n _ hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 1 z) (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0) y n x hp,
      horizontalJet_two_coordPartials hU hz hp n 0 1]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 0 z) (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0) y n x hp,
      horizontalJet_two_coordPartials hU hz hp n 0 0]
    rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QHighEquation
attribute [-simp] _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem sixVariableQ_direction (g : MetricField) (w v : DarbouxState) :
    fderiv ℝ (sixVariableQ g) w v = ∑ i : Fin 6, qFirstCoefficient g i w * v i := by
  conv_lhs => rw [finite_state_basis_decomposition v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index _
  simp only [map_smul, smul_eq_mul, qFirstCoefficient, mul_comm]

theorem sixVariableQ_zero_spatial_direction (g : MetricField) (w v : DarbouxState)
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    fderiv ℝ (sixVariableQ g) w v =
      qFirstCoefficient g 2 w * v 2 + qFirstCoefficient g 3 w * v 3 +
        qFirstCoefficient g 4 w * v 4 + qFirstCoefficient g 5 w * v 5 := by
  rw [sixVariableQ_direction]
  simp [Fin.sum_univ_succ, hv0, hv1, add_assoc]

theorem actualQ_single_linearization
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : coordinatePoint x y ∈ U)
    (n : ℕ) (hn : 2 ≤ n) :
    chainTerm (sixVariableQ g) (qSolutionJetCurve z y) (ChainWord.single n) x =
      qDirectLinearization g z (horizontalJet z n) (coordinatePoint x y) := by
  rw [chainTerm_single_eq, qSolutionJetCurve_iteratedDeriv hU hz hp n hn,
    sixVariableQ_zero_spatial_direction _ _ _ (by rfl) (by rfl)]
  rfl

theorem qChainTerm_eq_coordinateChainTerm
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : coordinatePoint x y ∈ U)
    (w : ChainWord) :
    chainTerm (sixVariableQ g) (qSolutionJetCurve z y) w x =
      qCoordinateChainTerm g z w (coordinatePoint x y) := by
  apply congrArg (iteratedFDeriv ℝ w.arity (sixVariableQ g) (qSolutionJet z (coordinatePoint x y)))
  funext i
  exact horizontalJet_slice hU (qSolutionJet_contDiffOn hU hz) y (w.order i) x hp

theorem qChainSum_eq_coordinateChainSum
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : coordinatePoint x y ∈ U)
    (ws : List ChainWord) :
    chainSum (sixVariableQ g) (qSolutionJetCurve z y) ws x =
      qCoordinateChainSum g z ws (coordinatePoint x y) := by
  unfold chainSum qCoordinateChainSum
  congr 1
  apply List.map_congr_left
  intro word _
  exact qChainTerm_eq_coordinateChainTerm hU hz hp word

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QResidualFactors
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem qCoordinateChainTerm_scalar_expansion (g : MetricField) (z : Coord → ℝ)
    (w : ChainWord) (p : Coord) :
    qCoordinateChainTerm g z w p = ∑ r : Fin w.arity → Fin 6,
      qCoordinateChainCoefficient g z w r p * ∏ i, qCoordinateChainFactor z w r i p :=
  multilinear_state_components _ _

theorem coordinate_qSolutionJet_horizontal_positive
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (n : ℕ) (hn : 0 < n) :
    horizontalJet (qSolutionJet z) n p =
      ![if n = 1 then 1 else 0, 0,
        spatialJet (spatialFirstJet z 0) n p, spatialJet (spatialFirstJet z 1) n p,
        spatialJet (spatialFirstJet z 1) (n + 1) p,
        spatialJet (spatialFirstJet z 0) (n + 1) p] := by
  have h := qSolutionJetCurve_iteratedDeriv_positive hU hz
    (x := p 0) (y := p 1) (by simpa only [point_eta] using hp) n hn
  have hs := horizontalJet_slice hU (qSolutionJet_contDiffOn hU hz) (p 1) n (p 0)
    (by simpa only [point_eta] using hp)
  change iteratedDeriv n (qSolutionJetCurve z (p 1)) (p 0) = _ at hs
  rw [hs] at h
  simpa only [point_eta] using h

theorem q_residual_factor_orders {m : ℕ} {w : ChainWord}
    (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) :
    (∀ i, qChainFactorOrder w r i ≤ m + 2) ∧ w.arity ≤ m + 3 := by
  obtain ⟨hpos, htotal, hbound⟩ := topResidualWords_properties m w hw
  constructor
  · intro i
    have ho := hbound i
    have hb := qFirstJetOffset_le_one (r i)
    unfold qChainFactorOrder
    omega
  · exact htotal ▸ ChainWord.arity_le_total hpos

theorem q_residual_high_unique {m : ℕ} (hm : 8 ≤ m + 3) {w : ChainWord}
    (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) {i j : Fin w.arity}
    (hi : m + 2 ≤ qChainFactorOrder w r i) (hj : m + 2 ≤ qChainFactorOrder w r j) : i = j :=
  topResidual_high_unique hm hw (fun k => qFirstJetOffset (r k))
    (fun k => (qFirstJetOffset_le_one (r k)).trans (by norm_num)) hi hj

theorem qCoordinateChainFactor_continuousOn
    {z : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (w : ChainWord) (r : Fin w.arity → Fin 6) (i : Fin w.arity) :
    ContinuousOn (qCoordinateChainFactor z w r i) U :=
  (ContinuousLinearMap.proj (r i) : DarbouxState →L[ℝ] ℝ).continuous.comp_continuousOn
    (horizontalJet_contDiffOn hU (qSolutionJet_contDiffOn hU hz) (w.order i)).continuousOn

theorem q_state_factor_low_bound
    {z : Coord → ℝ} {U : Set Coord} {theta left right lengthFloor : ℝ}
    {N : ℕ} {H : ℝ≥0}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right N H)
    (n : ℕ) (hn : 0 < n) (k : Fin 6) (horder : n + qFirstJetOffset k + 1 ≤ N)
    {x : ℝ} (hx : x ∈ Icc left right) :
    ‖horizontalJet (qSolutionJet z) n (coordinatePoint x theta) k‖ ≤
      spatialLowFactorBound lengthFloor H := by
  rw [coordinate_qSolutionJet_horizontal_positive hU hz (hseg x hx) n hn]
  have hB : 1 ≤ spatialLowFactorBound lengthFloor H := le_max_left _ _
  have hf (i : Fin 2) := partial_contDiffOn hz hU i
  have hlow (i : Fin 2) (j : ℕ) (hj : j + 1 ≤ N) :
      ‖spatialJet (spatialFirstJet z i) j (coordinatePoint x theta)‖ ≤
        spatialLowFactorBound lengthFloor H := by
    rw [Real.norm_eq_abs]
    exact (hL2.pointwise_below_top hU hf hseg hlength hwidth i j hj hx).trans (le_max_right _ _)
  fin_cases k
  · by_cases he : n = 1
    · simpa [he] using hB
    · simpa [he] using (zero_le_one.trans hB)
  · simpa using (zero_le_one.trans hB)
  · exact hlow 0 n (by simpa [qFirstJetOffset] using horder)
  · exact hlow 1 n (by simpa [qFirstJetOffset] using horder)
  · exact hlow 1 (n + 1) (by simpa [qFirstJetOffset] using horder)
  · exact hlow 0 (n + 1) (by simpa [qFirstJetOffset] using horder)

theorem q_state_factor_high_eLpNorm
    {z : Coord → ℝ} {U : Set Coord} {theta left right : ℝ} {N : ℕ} {H : ℝ≥0}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right N H)
    (n : ℕ) (hn : 0 < n) (hnlow : n < N) (k : Fin 6)
    (hhigh : N ≤ n + qFirstJetOffset k) (htop : n + qFirstJetOffset k ≤ N) :
    eLpNorm (fun x => horizontalJet (qSolutionJet z) n (coordinatePoint x theta) k) 2
      (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞) := by
  have he : (fun x => horizontalJet (qSolutionJet z) n (coordinatePoint x theta) k) =ᵐ[
      volume.restrict (Icc left right)] (fun x =>
      (![if n = 1 then 1 else 0, 0,
        spatialJet (spatialFirstJet z 0) n (coordinatePoint x theta),
        spatialJet (spatialFirstJet z 1) n (coordinatePoint x theta),
        spatialJet (spatialFirstJet z 1) (n + 1) (coordinatePoint x theta),
        spatialJet (spatialFirstJet z 0) (n + 1) (coordinatePoint x theta)] : DarbouxState) k) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact congrArg (fun w : DarbouxState => w k)
      (coordinate_qSolutionJet_horizontal_positive hU hz (hseg x hx) n hn)
  rw [eLpNorm_congr_ae he]
  fin_cases k
  · norm_num [qFirstJetOffset] at hhigh
    omega
  · norm_num [qFirstJetOffset] at hhigh
    omega
  · norm_num [qFirstJetOffset] at hhigh
    omega
  · norm_num [qFirstJetOffset] at hhigh
    omega
  · exact hL2 1 (n + 1) (by simpa [qFirstJetOffset] using htop)
  · exact hL2 0 (n + 1) (by simpa [qFirstJetOffset] using htop)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QResidualL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Analytic

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

theorem q_residual_product_eLpNorm_two
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {theta left right lengthFloor : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    {w : ChainWord} (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) :
    eLpNorm (fun x => ∏ i, qCoordinateChainFactor z w r i (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤
        spatialProductL2Budget lengthFloor left right H w.arity := by
  classical
  let B := spatialLowFactorBound lengthFloor H
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  obtain ⟨hpos, _, horders⟩ := topResidualWords_properties m w hw
  have hproductMeas := (smooth_slice_memLp_two
    (continuousOn_finsetProd Finset.univ (fun index _ =>
      qCoordinateChainFactor_continuousOn hU hz w r index)) hseg).aestronglyMeasurable
  have hfactorOrders := (q_residual_factor_orders hw r).1
  have hlow (i : Fin w.arity) (hi : qChainFactorOrder w r i + 1 ≤ m + 2)
      (x : ℝ) (hx : x ∈ Icc left right) :
      ‖qCoordinateChainFactor z w r i (coordinatePoint x theta)‖ ≤ B :=
    q_state_factor_low_bound hU hz hseg hlength hwidth hL2
      (w.order i) (hpos i) (r i) hi hx
  by_cases hh : ∃ j, m + 2 ≤ qChainFactorOrder w r j
  · obtain ⟨j, hj⟩ := hh
    have hb (i : Fin w.arity) (hi : i ∈ (Finset.univ : Finset (Fin w.arity)).erase j)
        (x : ℝ) (hx : x ∈ Icc left right) :
        ‖qCoordinateChainFactor z w r i (coordinatePoint x theta)‖ ≤ B := by
      apply hlow i _ x hx
      have hnot : ¬ m + 2 ≤ qChainFactorOrder w r i := fun hie =>
        (Finset.mem_erase.mp hi).1 (q_residual_high_unique hm hw r hie hj)
      omega
    have hjL2 : eLpNorm (fun x => qCoordinateChainFactor z w r j (coordinatePoint x theta)) 2
        (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞) :=
      q_state_factor_high_eLpNorm hU hz hseg hL2 (w.order j) (hpos j)
        (by have ho := horders j; omega) (r j) hj (hfactorOrders j)
    have hprod := finite_product_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (fun i x => qCoordinateChainFactor z w r i (coordinatePoint x theta))
      (Finset.mem_univ j) hB0 measurableSet_Icc hb hproductMeas
    have hcard : ((Finset.univ : Finset (Fin w.arity)).erase j).card ≤ w.arity := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.erase_subset j (Finset.univ : Finset (Fin w.arity)))
    have hpow : ‖B ^ ((Finset.univ : Finset (Fin w.arity)).erase j).card‖ₑ ≤ ‖B ^ w.arity‖ₑ := by
      rw [enorm_le_iff_norm_le, Real.norm_of_nonneg (pow_nonneg hB0 _),
        Real.norm_of_nonneg (pow_nonneg hB0 _)]
      exact pow_le_pow_right₀ hB1 hcard
    calc
      _ ≤ ‖B ^ ((Finset.univ : Finset (Fin w.arity)).erase j).card‖ₑ *
          eLpNorm (fun x => qCoordinateChainFactor z w r j (coordinatePoint x theta)) 2
            (volume.restrict (Icc left right)) := hprod
      _ ≤ ‖B ^ w.arity‖ₑ * (H : ℝ≥0∞) := mul_le_mul' hpow hjL2
      _ ≤ _ := mul_le_mul' le_rfl (le_add_of_nonneg_right (by positivity))
  · have hb (i : Fin w.arity) (_ : i ∈ (Finset.univ : Finset (Fin w.arity)))
        (x : ℝ) (hx : x ∈ Icc left right) :
        ‖qCoordinateChainFactor z w r i (coordinatePoint x theta)‖ ≤ B := by
      apply hlow i _ x hx
      have hnot : ¬ m + 2 ≤ qChainFactorOrder w r i := fun hie => hh ⟨i, hie⟩
      omega
    have hprod := finite_product_bounded_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (fun i x => qCoordinateChainFactor z w r i (coordinatePoint x theta))
      hB0 measurableSet_Icc hb hproductMeas
    calc
      _ ≤ ‖B ^ w.arity‖ₑ * (volume (Icc left right)) ^ (1 / (2 : ℝ)) := by
        simpa only [Finset.card_univ, Fintype.card_fin] using hprod
      _ ≤ _ := mul_le_mul' le_rfl (le_add_of_nonneg_left (by positivity))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QResidualActive
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Analytic

theorem q_state_factor_eq_zero_of_spatial_inactive
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (n : ℕ) (hn : 0 < n) (k : Fin 6) (hk : k = 1 ∨ (k = 0 ∧ n ≠ 1)) :
    horizontalJet (qSolutionJet z) n p k = 0 := by
  rw [coordinate_qSolutionJet_horizontal_positive hU hz hp n hn]
  rcases hk with hk | ⟨hk, hn1⟩
  · subst k
    rfl
  · subst k
    simp [hn1]

theorem qCoordinateChainProduct_eq_zero_of_inactive
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (w : ChainWord) (hpos : w.Positive) (r : Fin w.arity → Fin 6)
    (hinactive : ¬ QActiveComponents w r) :
    (∏ i, qCoordinateChainFactor z w r i p) = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hinactive
  have hbad : r i = 1 ∨ (r i = 0 ∧ w.order i ≠ 1) := by
    by_cases h1 : r i = 1
    · exact Or.inl h1
    · right
      have hh : ¬ (r i = 0 → w.order i = 1) := fun himp => hi ⟨h1, himp⟩
      by_cases hzero : r i = 0
      · exact ⟨hzero, fun horder => hh (fun _ => horder)⟩
      · exact (hh (fun heq => (hzero heq).elim)).elim
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (q_state_factor_eq_zero_of_spatial_inactive hU hz hp (w.order i) (hpos i) (r i) hbad)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_UniversalMetricQ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def universalQDenominator (a : MetricPInput) : ℝ :=
  a.2.2.2 5 - universalConnection a 0 0

def universalMetricQ (a : MetricPInput) : ℝ :=
  universalConnection a 1 1 +
    ((a.2.2.2 4 - universalConnection a 0 1)^2 +
      curvatureJet a.1 a.2.1 a.2.2.1 * universalEnergy a) / universalQDenominator a

def universalMetricQDomain : Set MetricPInput :=
  {a | a.1.det ≠ 0 ∧ universalQDenominator a ≠ 0}

def universalMetricQTube (M d c : ℝ) : Set MetricPInput :=
  universalMetricBaseTube M d ∩ universalQDenominator ⁻¹' {x : ℝ | c ≤ |x|}

theorem universalQDenominator_metricPBundle (g : MetricField) (w : DarbouxState) :
    universalQDenominator (metricPBundle g w) = stateQDenominator g w := rfl

theorem universalQDenominator_contDiffOn :
    ContDiffOn ℝ ∞ universalQDenominator universalMetricBase := by
  intro a ha
  exact ((show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 5) a by fun_prop).sub
    (universalConnection_contDiffAt ha 0 0)).contDiffWithinAt

theorem universalMetricQDomain_isOpen : IsOpen universalMetricQDomain :=
  universalQDenominator_contDiffOn.continuousOn.isOpen_inter_preimage
    universalMetricBase_isOpen isClosed_singleton.isOpen_compl

theorem universalMetricQ_contDiffOn :
    ContDiffOn ℝ ∞ universalMetricQ universalMetricQDomain := by
  intro a ha
  have hΓ := universalConnection_contDiffAt ha.1
  have hK : ContDiffAt ℝ ∞
      (fun b : MetricPInput => curvatureJet b.1 b.2.1 b.2.2.1) a :=
    curvatureJet_contDiffAt (fun i j => by fun_prop)
      (fun d i j => by fun_prop) (fun d e i j => by fun_prop) ha.1
  have hm : ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4 - universalConnection b 0 1) a :=
    (show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4) a by fun_prop).sub (hΓ 0 1)
  exact ((hΓ 1 1).add (((hm.pow 2).add (hK.mul universalEnergy_contDiff.contDiffAt)).div
    (universalQDenominator_contDiffOn.contDiffAt (universalMetricBase_isOpen.mem_nhds ha.1))
    ha.2)).contDiffWithinAt

theorem universalMetricQTube_isCompact (M : ℝ) {d : ℝ} (hd : 0 < d) (c : ℝ) :
    IsCompact (universalMetricQTube M d c) := by
  have hbase := universalMetricBaseTube_isCompact M d
  have hc : ContinuousOn universalQDenominator (universalMetricBaseTube M d) :=
    universalQDenominator_contDiffOn.continuousOn.mono (universalMetricBaseTube_subset_base M hd)
  have hclosed : IsClosed (universalMetricQTube M d c) :=
    hc.preimage_isClosed_of_isClosed hbase.isClosed (isClosed_le continuous_const continuous_abs)
  exact hbase.of_isClosed_subset hclosed inter_subset_left

theorem universalMetricQTube_subset_domain (M : ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    universalMetricQTube M d c ⊆ universalMetricQDomain := by
  intro a ha
  refine ⟨universalMetricBaseTube_subset_base M hd ha.1, ?_⟩
  intro hz
  have hh : c ≤ |universalQDenominator a| := ha.2
  rw [hz, abs_zero] at hh
  linarith

theorem universalMetricQTube_finite_bounds (M : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ N, ∀ a ∈ universalMetricQTube M d c,
      ‖iteratedFDeriv ℝ k universalMetricQ a‖ ≤ C := by
  classical
  have hk : ∀ k : Fin (N + 1), ∃ A : ℝ,
      ∀ a ∈ universalMetricQTube M d c, ‖iteratedFDeriv ℝ k.val universalMetricQ a‖ ≤ A := by
    intro k
    have hcont : ContinuousOn (iteratedFDeriv ℝ k.val universalMetricQ) universalMetricQDomain := by
      apply (universalMetricQ_contDiffOn.continuousOn_iteratedFDerivWithin
        (WithTop.coe_le_coe.mpr le_top) universalMetricQDomain_isOpen.uniqueDiffOn).congr
      intro a ha
      exact (iteratedFDerivWithin_eq_iteratedFDeriv universalMetricQDomain_isOpen.uniqueDiffOn
        ((universalMetricQ_contDiffOn.contDiffAt
          (universalMetricQDomain_isOpen.mem_nhds ha)).of_le (WithTop.coe_le_coe.mpr le_top)) ha).symm
    exact (universalMetricQTube_isCompact M hd c).exists_bound_of_continuousOn
      (hcont.mono (universalMetricQTube_subset_domain M hd hc))
  choose A hA using hk
  refine ⟨∑ k : Fin (N + 1), |A k|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro k hk a ha
  let j : Fin (N + 1) := ⟨k, by omega⟩
  exact (hA j a ha).trans ((le_abs_self (A j)).trans
    (Finset.single_le_sum (fun index _ => abs_nonneg (A index)) (Finset.mem_univ j)))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricQSpatialBundle
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

def metricQSpatialBundle (g : MetricField) (theta : ℝ) : QSpatialState → MetricPInput :=
  metricPBundle g ∘ qFixedTimeState theta

theorem norm_iteratedFDeriv_fixedTime_coordinate
    {f : Coord → ℝ} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {theta : ℝ} {v : QSpatialState} (hp : coordinatePoint (v 0) theta ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun w : QSpatialState => f (coordinatePoint (w 0) theta)) v‖ ≤
      |horizontalJet f n (coordinatePoint (v 0) theta)| := by
  let I : Set ℝ := {x | coordinatePoint x theta ∈ U}
  let L : QSpatialState →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hI : IsOpen I := hU.preimage (horizontalPoint_contDiff theta).continuous
  have hs : ContDiffOn ℝ ∞ (fun x : ℝ => f (coordinatePoint x theta)) I :=
    hf.comp (horizontalPoint_contDiff theta).contDiffOn (fun x hx => hx)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    simpa only [one_mul, L, ContinuousLinearMap.proj_apply] using norm_le_pi_norm w 0
  have h := norm_iteratedFDeriv_comp_contraction L hs hI hL hp n
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  change ‖iteratedFDeriv ℝ n (fun w : QSpatialState => f (coordinatePoint (w 0) theta)) v‖ ≤
    ‖iteratedDeriv n (fun x => f (coordinatePoint x theta)) (v 0)‖ at h
  rw [horizontalJet_slice hU hf theta n (v 0) hp, Real.norm_eq_abs] at h
  exact h

theorem metricQSpatialBundle_norm_bound
    {g : MetricField} {theta G W : ℝ} {v : QSpatialState} {N : ℕ}
    (hG : 0 ≤ G) (hgB : HorizontalMetricTwoJetBound g (coordinatePoint (v 0) theta) N G)
    (hwB : ‖qFixedTimeState theta v‖ ≤ W) :
    ‖metricQSpatialBundle g theta v‖ ≤ max G W := by
  have h0 : ‖g (coordinatePoint (v 0) theta)‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hgB.1 i j 0 (by omega)))
  have h1 : ‖(fun d i j => coordPartial d (fun p => g p i j) (coordinatePoint (v 0) theta))‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun d =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
        (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hgB.2.1 d i j 0 (by omega))))
  have h2 : ‖(fun d e i j => coordPartial d (coordPartial e (fun p => g p i j))
      (coordinatePoint (v 0) theta))‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun d =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun e =>
        (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
          (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hgB.2.2 d e i j 0 (by omega)))))
  unfold metricQSpatialBundle metricPBundle
  simp only [Function.comp_apply, statePoint_qFixedTimeState, Prod.norm_def]
  exact max_le (h0.trans (le_max_left _ _))
    (max_le (h1.trans (le_max_left _ _))
      (max_le (h2.trans (le_max_left _ _)) (hwB.trans (le_max_right _ _))))

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

theorem metricQSpatialBundle_mapsTo_domain {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (theta : ℝ) :
    MapsTo (metricQSpatialBundle g theta) (qFixedTimeDomain g U theta) universalMetricQDomain := by
  intro v hv
  exact ⟨metricDet_ne_zero hg hv.1,
    by simpa only [metricQSpatialBundle, Function.comp_apply, universalQDenominator_metricPBundle] using hv.2⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QFirstSpatialBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem coordPartial_qSolutionJet_xi_norm_bound
    {z : Coord → ℝ} {U S : Set Coord} {Z : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hSU : S ⊆ U)
    (hzB : CoordinateBound z S 3 Z) {p : Coord} (hp : p ∈ S) :
    ‖coordPartial 0 (qSolutionJet z) p‖ ≤ max 1 Z := by
  have he := coordinate_qSolutionJet_horizontal_positive hU hz (hSU hp) 1 (by norm_num)
  change coordPartial 0 (qSolutionJet z) p = _ at he
  rw [he]
  apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans (le_max_left _ _))).mpr
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · simp
  · simp
  · exact (hzB [0, 0] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 0, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 0, 0] (by norm_num) p hp).trans (le_max_right _ _)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QFirstJetEnergy
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem spatialFirstJet_slice_eLpNorm_two_of_energy
    {z S : Coord → ℝ} {U : Set Coord} {left right theta s0 : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hS : ContDiffOn ℝ ∞ S U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlr : left ≤ right) (hs0 : 0 < s0)
    (hfloor : ∀ x ∈ Icc left right, s0 ≤ S (coordinatePoint x theta))
    (ell : ℕ) (A : ℝ≥0)
    (henergy : Real.sqrt (∫ x in left..right,
      energyDensity S (horizontalJet z ell) (coordinatePoint x theta)) ≤ (A : ℝ))
    (i : Fin 2) :
    eLpNorm (fun x => spatialJet (spatialFirstJet z i) ell (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ (spatialEnergyNormBudget s0 A : ℝ≥0∞) := by
  let u := horizontalJet z ell
  let E := ∫ x in left..right, energyDensity S u (coordinatePoint x theta)
  let C := 2 * (1 + 1 / s0)
  have hC : 0 ≤ C := by dsimp [C] <;> positivity
  have hu := horizontalJet_contDiffOn hU hz ell
  have hd (j : Fin 2) := partial_contDiffOn hu hU j
  have he : ContDiffOn ℝ ∞ (energyDensity S u) U :=
    (((hd 1).pow 2).add (hS.mul ((hd 0).pow 2))).div_const 2
  have hEA : E ≤ (A : ℝ)^2 := (Real.sqrt_le_iff.mp henergy).2
  have hfiCont : ContinuousOn (fun x => coordPartial i u (coordinatePoint x theta)^2) (Icc left right) :=
    ((hd i).pow 2).continuousOn.comp (horizontalPoint_contDiff theta).continuous.continuousOn hseg
  have heCont : ContinuousOn (fun x => C * energyDensity S u (coordinatePoint x theta)) (Icc left right) :=
    (continuousOn_const.mul he.continuousOn).comp (horizontalPoint_contDiff theta).continuous.continuousOn hseg
  have hiInt : (∫ x in left..right, coordPartial i u (coordinatePoint x theta)^2) ≤ C * E := by
    have hh : (∫ x in left..right, coordPartial i u (coordinatePoint x theta)^2) ≤
        ∫ x in left..right, C * energyDensity S u (coordinatePoint x theta) :=
      intervalIntegral.integral_mono_on hlr
      (hfiCont.intervalIntegrable_of_Icc hlr) (heCont.intervalIntegrable_of_Icc hlr)
      (fun x hx => show coordPartial i u (coordinatePoint x theta)^2 ≤
          C * energyDensity S u (coordinatePoint x theta) from by
        have hscalar := scalar_gradient_le_energy hs0 (hfloor x hx)
          (a := coordPartial 1 u (coordinatePoint x theta)) (b := coordPartial 0 u (coordinatePoint x theta))
        have hind : coordPartial i u (coordinatePoint x theta)^2 ≤
            coordPartial 1 u (coordinatePoint x theta)^2 + coordPartial 0 u (coordinatePoint x theta)^2 := by
          fin_cases i
          · change coordPartial 0 u (coordinatePoint x theta)^2 ≤ _
            nlinarith [sq_nonneg (coordPartial 1 u (coordinatePoint x theta))]
          · change coordPartial 1 u (coordinatePoint x theta)^2 ≤ _
            nlinarith [sq_nonneg (coordPartial 0 u (coordinatePoint x theta))]
        exact hind.trans hscalar)
    simpa only [intervalIntegral.integral_const_mul] using hh
  have hiBudget : (∫ x in left..right, coordPartial i u (coordinatePoint x theta)^2) ≤
      (spatialEnergyNormBudget s0 A : ℝ)^2 := by
    have hbound := hiInt.trans (mul_le_mul_of_nonneg_left hEA hC)
    change _ ≤ (Real.sqrt C * (A : ℝ))^2
    rw [mul_pow, Real.sq_sqrt hC]
    exact hbound
  have hiLp := real_slice_eLpNorm_two_le_of_square_integral hlr
    (smooth_slice_memLp_two (hd i).continuousOn hseg) hiBudget
  have heq : (fun x => spatialJet (spatialFirstJet z i) ell (coordinatePoint x theta)) =ᵐ[
      volume.restrict (Icc left right)] (fun x => coordPartial i u (coordinatePoint x theta)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [← horizontalJet_eq_spatialJet]
    exact horizontalJet_coordPartial hU hz i ell _ (hseg x hx)
  rw [eLpNorm_congr_ae heq]
  exact hiLp

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QInitialEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Interval NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem initial_energy_bound_of_cut_jets
    {z S : Coord → ℝ} {U : Set Coord} {left right theta M : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hS : ContDiffOn ℝ ∞ S U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlr : left ≤ right) (hM : 0 ≤ M)
    (hSupper : ∀ x ∈ Icc left right, S (coordinatePoint x theta) ≤ M)
    (ell : ℕ) (A : ℝ≥0)
    (hcut : ∀ ds : List (Fin 2), ds.length ≤ ell + 1 → ∀ x ∈ Icc left right,
      |iteratedCoordPartial ds z (coordinatePoint x theta)| ≤ (A : ℝ)) :
    Real.sqrt (∫ x in left..right,
      energyDensity S (horizontalJet z ell) (coordinatePoint x theta)) ≤
        (initialCutEnergyBudget (right - left) M A : ℝ) := by
  let u := horizontalJet z ell
  have hu := horizontalJet_contDiffOn hU hz ell
  have hd (i : Fin 2) := partial_contDiffOn hu hU i
  have hb (i : Fin 2) (x : ℝ) (hx : x ∈ Icc left right) :
      |coordPartial i u (coordinatePoint x theta)| ≤ (A : ℝ) := by
    have he : coordPartial i u (coordinatePoint x theta) =
        iteratedCoordPartial (List.replicate ell 0 ++ [i]) z (coordinatePoint x theta) := by
      rw [← horizontalJet_coordPartial hU hz i ell _ (hseg x hx), horizontalJet_eq_spatialJet]
      exact congrFun (spatialJet_firstJet_eq_word z ell i) _
    rw [he]
    apply hcut _ _ x hx
    simp only [List.length_append, List.length_replicate, List.length_singleton, le_refl]
  have hpoint (x : ℝ) (hx : x ∈ Icc left right) :
      energyDensity S u (coordinatePoint x theta) ≤ (1 + M) * (A : ℝ)^2 / 2 := by
    have h0 : coordPartial 0 u (coordinatePoint x theta)^2 ≤ (A : ℝ)^2 := by
      exact sq_le_sq.mpr ((hb 0 x hx).trans (le_abs_self _))
    have h1 : coordPartial 1 u (coordinatePoint x theta)^2 ≤ (A : ℝ)^2 := by
      exact sq_le_sq.mpr ((hb 1 x hx).trans (le_abs_self _))
    have hm := mul_le_mul (hSupper x hx) h0 (sq_nonneg _) hM
    unfold energyDensity
    nlinarith
  have he : ContDiffOn ℝ ∞ (energyDensity S u) U :=
    (((hd 1).pow 2).add (hS.mul ((hd 0).pow 2))).div_const 2
  have hcont : ContinuousOn (fun x => energyDensity S u (coordinatePoint x theta)) (Icc left right) :=
    he.continuousOn.comp (horizontalPoint_contDiff theta).continuous.continuousOn hseg
  have hi : (∫ x in left..right, energyDensity S u (coordinatePoint x theta)) ≤
      ∫ x in left..right, (1 + M) * (A : ℝ)^2 / 2 :=
    intervalIntegral.integral_mono_on hlr (hcont.intervalIntegrable_of_Icc hlr)
    intervalIntegrable_const hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  apply (Real.sqrt_le_left (initialCutEnergyBudget (right - left) M A).2).mpr
  change _ ≤ (Real.sqrt ((right - left) * (1 + M) / 2) * (A : ℝ))^2
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (right - left) * (1 + M) / 2)]
  nlinarith

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_StateCoefficientTube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem stateBaseCompact_isCompact {S : Set Coord} (hS : IsCompact S) (M : ℝ) :
    IsCompact (stateBaseCompact S M) :=
  isCompact_Icc.inter_left (hS.isClosed.preimage statePoint_contDiff.continuous)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_LocalMetricQFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem metricPBundle_mapsTo_Q_domain {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) :
    MapsTo (metricPBundle g) (darbouxQStateDomain g U) universalMetricQDomain := by
  intro w hw
  exact ⟨metricDet_ne_zero hg hw.1,
    by simpa only [universalQDenominator_metricPBundle] using hw.2⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QLowActualBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem coordPartial_qSolutionJet_norm_bound
    {z : Coord → ℝ} {U S : Set Coord} {Z : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hSU : S ⊆ U)
    (hzB : CoordinateBound z S 3 Z) {p : Coord} (hp : p ∈ S) (j : Fin 2) :
    ‖coordPartial j (qSolutionJet z) p‖ ≤ max 1 Z := by
  have hJ : DifferentiableAt ℝ (qSolutionJet z) p :=
    ((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds (hSU hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he (i : Fin 6) : coordPartial j (qSolutionJet z) p i =
      coordPartial j (fun r => qSolutionJet z r i) p := by
    unfold coordPartial
    rw [fderiv_apply hJ i]
    rfl
  apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans (le_max_left _ _))).mpr
  intro i
  rw [he, Real.norm_eq_abs]
  fin_cases i
  · change |coordPartial j (fun r : Coord => r 0) p| ≤ max 1 Z
    rw [DarbouxJetCalculus.coordPartial_eval]
    split_ifs <;> simp only [abs_one, abs_zero]
    · exact le_max_left _ _
    · exact zero_le_one.trans (le_max_left _ _)
  · change |coordPartial j (fun r : Coord => r 1) p| ≤ max 1 Z
    rw [DarbouxJetCalculus.coordPartial_eval]
    split_ifs <;> simp only [abs_one, abs_zero]
    · exact le_max_left _ _
    · exact zero_le_one.trans (le_max_left _ _)
  · change |iteratedCoordPartial [j, 0] z p| ≤ max 1 Z
    exact (hzB [j, 0] (by norm_num) p hp).trans (le_max_right _ _)
  · change |iteratedCoordPartial [j, 1] z p| ≤ max 1 Z
    exact (hzB [j, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · change |iteratedCoordPartial [j, 0, 1] z p| ≤ max 1 Z
    exact (hzB [j, 0, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · change |iteratedCoordPartial [j, 0, 0] z p| ≤ max 1 Z
    exact (hzB [j, 0, 0] (by norm_num) p hp).trans (le_max_right _ _)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_UniversalQRaw
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

def universalQCurvature (a : MetricPInput) : ℝ :=
  curvatureJet a.1 a.2.1 a.2.2.1

def universalQNumerator (a : MetricPInput) : ℝ :=
  (a.2.2.2 4 - universalConnection a 0 1)^2 +
    universalQCurvature a * universalEnergy a

def universalQRaw (a : MetricPInput) : Fin 4 → ℝ :=
  ![universalQDenominator a, universalEnergy a,
    universalQNumerator a, universalQCurvature a]

theorem universalQCurvature_contDiffOn :
    ContDiffOn ℝ ∞ universalQCurvature universalMetricBase := by
  intro a ha
  exact (curvatureJet_contDiffAt (fun i j => by fun_prop)
    (fun d i j => by fun_prop) (fun d e i j => by fun_prop) ha).contDiffWithinAt

theorem universalQNumerator_contDiffOn :
    ContDiffOn ℝ ∞ universalQNumerator universalMetricBase := by
  intro a ha
  have hm : ContDiffAt ℝ ∞
      (fun b : MetricPInput => b.2.2.2 4 - universalConnection b 0 1) a :=
    (show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4) a by fun_prop).sub
      (universalConnection_contDiffAt ha 0 1)
  exact ((hm.pow 2).add
    ((universalQCurvature_contDiffOn.contDiffAt (universalMetricBase_isOpen.mem_nhds ha)).mul
      universalEnergy_contDiff.contDiffAt)).contDiffWithinAt

theorem universalQRaw_contDiffOn :
    ContDiffOn ℝ ∞ universalQRaw universalMetricBase := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact universalQDenominator_contDiffOn
  · exact universalEnergy_contDiff.contDiffOn
  · exact universalQNumerator_contDiffOn
  · exact universalQCurvature_contDiffOn

theorem universalQRaw_uniform_error (M : ℝ) {d error : ℝ}
    (hd : 0 < d) (he : 0 < error) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ a ∈ universalMetricBaseTube M d,
      ∀ b ∈ universalMetricBaseTube M d, ‖b - a‖ ≤ epsilon →
        ∀ i : Fin 4, |universalQRaw b i - universalQRaw a i| ≤ error := by
  have hc := (universalMetricBaseTube_isCompact M d).uniformContinuousOn_of_continuous
    (universalQRaw_contDiffOn.continuousOn.mono (universalMetricBaseTube_subset_base M hd))
  obtain ⟨epsilon, hepsilon, herror⟩ := Metric.uniformContinuousOn_iff_le.mp hc error he
  refine ⟨epsilon, hepsilon, ?_⟩
  intro a ha b hb hab i
  have hn : ‖universalQRaw b - universalQRaw a‖ ≤ error := by
    simpa only [dist_eq_norm] using herror b hb a ha (by simpa only [dist_eq_norm] using hab)
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    (norm_le_pi_norm (universalQRaw b - universalQRaw a) i).trans hn

theorem universalQDenominator_uniform_bound (M : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ a ∈ universalMetricBaseTube M d,
      |universalQDenominator a| ≤ A := by
  obtain ⟨C, hC⟩ := (universalMetricBaseTube_isCompact M d).exists_bound_of_continuousOn
    (universalQDenominator_contDiffOn.continuousOn.mono
      (universalMetricBaseTube_subset_base M hd))
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro a ha
  simpa only [Real.norm_eq_abs] using (hC a ha).trans (le_max_right 1 C)

theorem universalQRaw_uniform_margins (M : ℝ) {d nu eta beta kappa : ℝ}
    (hd : 0 < d) (hnu : 0 < nu) (heta : 0 < eta) (hbeta : 0 < beta)
    (hkappa : 0 < kappa) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ a ∈ universalMetricBaseTube M d,
      ∀ b ∈ universalMetricBaseTube M d, ‖b - a‖ ≤ epsilon →
      nu ≤ |universalQDenominator a| → eta ≤ universalEnergy a →
      universalQNumerator a ≤ -beta → universalQCurvature a ≤ -kappa →
      nu / 2 ≤ |universalQDenominator b| ∧ eta / 2 ≤ universalEnergy b ∧
      universalQNumerator b ≤ -(beta / 2) ∧ universalQCurvature b ≤ -(kappa / 2) := by
  let error := min (nu / 2) (min (eta / 2) (min (beta / 2) (kappa / 2)))
  have he : 0 < error := lt_min (half_pos hnu)
    (lt_min (half_pos heta) (lt_min (half_pos hbeta) (half_pos hkappa)))
  obtain ⟨epsilon, hepsilon, herror⟩ := universalQRaw_uniform_error M hd he
  refine ⟨epsilon, hepsilon, ?_⟩
  intro a ha b hb hab hden henergy hnum hK
  have h0 := herror a ha b hb hab 0
  have h1 := herror a ha b hb hab 1
  have h2 := herror a ha b hb hab 2
  have h3 := herror a ha b hb hab 3
  change |universalQDenominator b - universalQDenominator a| ≤ error at h0
  change |universalEnergy b - universalEnergy a| ≤ error at h1
  change |universalQNumerator b - universalQNumerator a| ≤ error at h2
  change |universalQCurvature b - universalQCurvature a| ≤ error at h3
  have he0 : error ≤ nu / 2 := min_le_left _ _
  have he1 : error ≤ eta / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have he2 : error ≤ beta / 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have he3 : error ≤ kappa / 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hdenerror := (abs_sub_abs_le_abs_sub (universalQDenominator a)
    (universalQDenominator b)).trans (by simpa only [abs_sub_comm] using h0)
  exact ⟨by linarith, by linarith [(abs_le.mp h1).1],
    by linarith [(abs_le.mp h2).2], by linarith [(abs_le.mp h3).2]⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QStripJetControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem qSolutionJet_eq_of_cauchy_data {z z0 : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hz0 : ContDiffOn ℝ ∞ z0 U) (hU : IsOpen U)
    {left right a : ℝ}
    (hline : ∀ x ∈ Ioo left right, boxPoint x a ∈ U)
    (hvalue : ∀ x ∈ Ioo left right, z0 (boxPoint x a) = z (boxPoint x a))
    (hvelocity : ∀ x ∈ Ioo left right,
      coordPartial 1 z0 (boxPoint x a) = coordPartial 1 z (boxPoint x a))
    {x : ℝ} (hx : x ∈ Ioo left right) :
    qSolutionJet z0 (boxPoint x a) = qSolutionJet z (boxPoint x a) := by
  have hxfirst : ∀ x ∈ Ioo left right,
      coordPartial 0 z0 (boxPoint x a) = coordPartial 0 z (boxPoint x a) :=
    fun x hx => horizontal_partial_eq_of_slice_eq hz hz0 hU hline hvalue hx
  have hxx := horizontal_partial_eq_of_slice_eq (partial_contDiffOn hz hU 0)
    (partial_contDiffOn hz0 hU 0) hU hline hxfirst hx
  have hxy := horizontal_partial_eq_of_slice_eq (partial_contDiffOn hz hU 1)
    (partial_contDiffOn hz0 hU 1) hU hline hvelocity hx
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact hxfirst x hx
  · exact hvelocity x hx
  · exact hxy
  · exact hxx

theorem coordinate_word_vertical_variation {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {left right a b x t : ℝ}
    (hbox : closedRectangle left right a b ⊆ U)
    (hx : x ∈ Icc left right) (hab : a ≤ b) (ht : t ∈ Icc a b)
    {M : ℝ} (hB : CoordinateBound f (closedRectangle left right a b) 3 M)
    (ds : List (Fin 2)) (hds : ds.length ≤ 2) :
    |iteratedCoordPartial ds f (boxPoint x t) -
      iteratedCoordPartial ds f (boxPoint x a)| ≤ M * |t - a| := by
  have hd (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivAt (fun y => iteratedCoordPartial ds f (boxPoint x y))
        (coordPartial 1 (iteratedCoordPartial ds f) (boxPoint x s)) s :=
    (LowQuotient.iterated_differentiableAt hf hU (hbox (boxPoint_mem hx hs)) ds).hasFDerivAt.comp_hasDerivAt
      s (boxPoint_hasDerivAt_s x s)
  have hb (s : ℝ) (hs : s ∈ Icc a b) :
      ‖deriv (fun y => iteratedCoordPartial ds f (boxPoint x y)) s‖ ≤ M := by
    rw [(hd s hs).deriv, Real.norm_eq_abs]
    exact hB (1 :: ds) (Nat.succ_le_succ hds) _ (boxPoint_mem hx hs)
  simpa only [Real.norm_eq_abs] using
    (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
      (fun s hs => (hd s hs).differentiableAt) hb (show a ∈ Icc a b from ⟨le_rfl, hab⟩) ht

theorem coordinate_word_difference_on_strip {z z0 : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hz0 : ContDiffOn ℝ ∞ z0 U) (hU : IsOpen U)
    {left right a b x t : ℝ}
    (hbox : closedRectangle left right a b ⊆ U)
    (hx : x ∈ Icc left right) (hab : a ≤ b) (ht : t ∈ Icc a b)
    {M M0 : ℝ} (hB : CoordinateBound z (closedRectangle left right a b) 3 M)
    (hB0 : CoordinateBound z0 (closedRectangle left right a b) 3 M0)
    (ds : List (Fin 2)) (hds : ds.length ≤ 2)
    (hinitial : iteratedCoordPartial ds z0 (boxPoint x a) =
      iteratedCoordPartial ds z (boxPoint x a)) :
    |iteratedCoordPartial ds z0 (boxPoint x t) - iteratedCoordPartial ds z (boxPoint x t)| ≤
      (M + M0) * |t - a| := by
  have h0 := coordinate_word_vertical_variation hz0 hU hbox hx hab ht hB0 ds hds
  have h1 := coordinate_word_vertical_variation hz hU hbox hx hab ht hB ds hds
  calc
    _ = |(iteratedCoordPartial ds z0 (boxPoint x t) - iteratedCoordPartial ds z0 (boxPoint x a)) -
      (iteratedCoordPartial ds z (boxPoint x t) - iteratedCoordPartial ds z (boxPoint x a))| := by
      rw [hinitial]
      congr 1
      ring
    _ ≤ |iteratedCoordPartial ds z0 (boxPoint x t) - iteratedCoordPartial ds z0 (boxPoint x a)| +
      |iteratedCoordPartial ds z (boxPoint x t) - iteratedCoordPartial ds z (boxPoint x a)| := abs_sub _ _
    _ ≤ M0 * |t - a| + M * |t - a| := add_le_add h0 h1
    _ = (M + M0) * |t - a| := by ring

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorSeparatedProduct
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem taylorCorrection_partial_xx {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 0 (coordPartial 0 (taylorCorrection C a n)) p =
      separatedProduct (deriv (deriv C)) (normalizedTimePower a (n + 2)) p := by
  have heq : coordPartial 0 (taylorCorrection C a n) =ᶠ[𝓝 p]
      separatedProduct (deriv C) (normalizedTimePower a (n + 2)) := by
    filter_upwards [(spatialStrip_isOpen hI).mem_nhds hp] with q hq
    exact taylorCorrection_partial_x hC hI a n hq
  rw [coordPartial_eq_of_eventuallyEq heq 0]
  exact separatedProduct_partial_x (hC.deriv_of_isOpen hI (by simp)) hI _
    (normalizedTimePower_contDiff a (n + 2)) hp

theorem taylorCorrection_partial_xt {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 0 (coordPartial 1 (taylorCorrection C a n)) p =
      separatedProduct (deriv C) (normalizedTimePower a (n + 1)) p := by
  have heq : coordPartial 1 (taylorCorrection C a n) =ᶠ[𝓝 p]
      separatedProduct C (normalizedTimePower a (n + 1)) := by
    filter_upwards [(spatialStrip_isOpen hI).mem_nhds hp] with q hq
    exact taylorCorrection_partial_t hC hI a n hq
  rw [coordPartial_eq_of_eventuallyEq heq 0]
  exact separatedProduct_partial_x hC hI _ (normalizedTimePower_contDiff a (n + 1)) hp

theorem taylorCorrection_partial_tt {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 1 (coordPartial 1 (taylorCorrection C a n)) p =
      separatedProduct C (normalizedTimePower a n) p := by
  have heq : coordPartial 1 (taylorCorrection C a n) =ᶠ[𝓝 p]
      separatedProduct C (normalizedTimePower a (n + 1)) := by
    filter_upwards [(spatialStrip_isOpen hI).mem_nhds hp] with q hq
    exact taylorCorrection_partial_t hC hI a n hq
  rw [coordPartial_eq_of_eventuallyEq heq 1,
    separatedProduct_partial_t hC hI _ (normalizedTimePower_contDiff a (n + 1)) hp,
    normalizedTimePower_deriv]
  rfl

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorJetStability
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem secondCoordPartial_add {P R : Coord → ℝ} {V : Set Coord}
    (hV : IsOpen V) (hP : ContDiffOn ℝ ∞ P V) (hR : ContDiffOn ℝ ∞ R V)
    {p : Coord} (hp : p ∈ V) (i j : Fin 2) :
    coordPartial i (coordPartial j (fun q => P q + R q)) p =
      coordPartial i (coordPartial j P) p + coordPartial i (coordPartial j R) p := by
  have he : coordPartial j (fun q => P q + R q) =ᶠ[𝓝 p]
      (fun q => coordPartial j P q + coordPartial j R q) := by
    filter_upwards [hV.mem_nhds hp] with q hq
    exact HessianCalculus.coordPartial_add_at
      ((hP.contDiffAt (hV.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      ((hR.contDiffAt (hV.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) j
  rw [coordPartial_eq_of_eventuallyEq he i]
  exact HessianCalculus.coordPartial_add_at
    (((partial_contDiffOn hP hV j).contDiffAt (hV.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (((partial_contDiffOn hR hV j).contDiffAt (hV.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) i

def correctionState (C : ℝ → ℝ) (a : ℝ) (n : ℕ) (p : Coord) : DarbouxState :=
  ![0, 0,
    deriv C (p 0) * normalizedTimePower a (n + 2) (p 1),
    C (p 0) * normalizedTimePower a (n + 1) (p 1),
    deriv C (p 0) * normalizedTimePower a (n + 1) (p 1),
    deriv (deriv C) (p 0) * normalizedTimePower a (n + 2) (p 1)]

theorem correctionState_slice_contDiff (C : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ) :
    ContDiff ℝ ∞ (fun t => correctionState C a n ![x, t]) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · change ContDiff ℝ ∞ (fun t => deriv C x * normalizedTimePower a (n + 2) t)
    exact contDiff_const.mul (normalizedTimePower_contDiff a (n + 2))
  · change ContDiff ℝ ∞ (fun t => C x * normalizedTimePower a (n + 1) t)
    exact contDiff_const.mul (normalizedTimePower_contDiff a (n + 1))
  · change ContDiff ℝ ∞ (fun t => deriv C x * normalizedTimePower a (n + 1) t)
    exact contDiff_const.mul (normalizedTimePower_contDiff a (n + 1))
  · change ContDiff ℝ ∞ (fun t => deriv (deriv C) x * normalizedTimePower a (n + 2) t)
    exact contDiff_const.mul (normalizedTimePower_contDiff a (n + 2))

theorem correctionState_time_jets_zero (C : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ)
    (k : ℕ) (hk : k ≤ n) :
    iteratedDeriv k (fun t => correctionState C a n ![x, t]) a = 0 := by
  ext i
  rw [iteratedDeriv_state_eval (correctionState_slice_contDiff C a n x).contDiffAt k i]
  fin_cases i
  · exact iteratedDeriv_fun_const_zero
  · exact iteratedDeriv_fun_const_zero
  · change iteratedDeriv k (fun t => deriv C x * normalizedTimePower a (n + 2) t) a = 0
    rw [coefficient_timePower_jet, ite_eq_right (by omega)]
  · change iteratedDeriv k (fun t => C x * normalizedTimePower a (n + 1) t) a = 0
    rw [coefficient_timePower_jet, ite_eq_right (by omega)]
  · change iteratedDeriv k (fun t => deriv C x * normalizedTimePower a (n + 1) t) a = 0
    rw [coefficient_timePower_jet, ite_eq_right (by omega)]
  · change iteratedDeriv k (fun t => deriv (deriv C) x * normalizedTimePower a (n + 2) t) a = 0
    rw [coefficient_timePower_jet, ite_eq_right (by omega)]

theorem qSolutionJet_add_taylorCorrection {P : Coord → ℝ} {C : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    qSolutionJet (fun q => P q + taylorCorrection C a n q) p =
      qSolutionJet P p + correctionState C a n p := by
  have hV := spatialStrip_isOpen hI
  have hR := taylorCorrection_contDiffOn hC a n
  have hdP := (hP.contDiffAt (hV.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdR := (hR.contDiffAt (hV.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  ext i
  fin_cases i
  · exact (add_zero (p 0)).symm
  · exact (add_zero (p 1)).symm
  · change coordPartial 0 (fun q => P q + taylorCorrection C a n q) p = _
    rw [HessianCalculus.coordPartial_add_at hdP hdR 0,
      taylorCorrection_partial_x hC hI a n hp]
    rfl
  · change coordPartial 1 (fun q => P q + taylorCorrection C a n q) p = _
    rw [HessianCalculus.coordPartial_add_at hdP hdR 1,
      taylorCorrection_partial_t hC hI a n hp]
    rfl
  · change coordPartial 0 (coordPartial 1 (fun q => P q + taylorCorrection C a n q)) p = _
    rw [secondCoordPartial_add hV hP hR hp 0 1,
      taylorCorrection_partial_xt hC hI a n hp]
    rfl
  · change coordPartial 0 (coordPartial 0 (fun q => P q + taylorCorrection C a n q)) p = _
    rw [secondCoordPartial_add hV hP hR hp 0 0,
      taylorCorrection_partial_xx hC hI a n hp]
    rfl

theorem qSolutionJet_time_slice_contDiffAt {P : Coord → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    {x : ℝ} (hx : x ∈ I) (a : ℝ) :
    ContDiffAt ℝ ∞ (fun t => qSolutionJet P ![x, t]) a :=
  ((qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).contDiffAt
    ((spatialStrip_isOpen hI).mem_nhds hx)).comp a (verticalPoint_contDiff x).contDiffAt

theorem qSolutionJet_taylorCorrection_time_jets
    {P : Coord → ℝ} {C : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ I) :
    ∀ k ≤ n,
      iteratedDeriv k (fun t => qSolutionJet
        (fun q => P q + taylorCorrection C a n q) ![x, t]) a =
      iteratedDeriv k (fun t => qSolutionJet P ![x, t]) a := by
  have he : (fun t => qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, t]) =
      (fun t => qSolutionJet P ![x, t] + correctionState C a n ![x, t]) := by
    funext t
    exact qSolutionJet_add_taylorCorrection hI hP hC a n hx
  rw [he]
  exact iteratedDeriv_add_eq_of_zero_jets
    (qSolutionJet_time_slice_contDiffAt hI hP hx a)
    (correctionState_slice_contDiff C a n x).contDiffAt
    (fun k hk => correctionState_time_jets_zero C a n x k hk)

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

def comparisonDomain (g : MetricField) (U : Set Coord) (P : Coord → ℝ)
    (I : Set ℝ) : Set Coord :=
  spatialStrip I ∩ qSolutionJet P ⁻¹' darbouxQStateDomain g U

theorem mem_comparisonDomain {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} {p : Coord}
    (hpI : p ∈ spatialStrip I) (hpU : p ∈ U) (hxx : covHessian g P p 0 0 ≠ 0) :
    p ∈ comparisonDomain g U P I :=
  ⟨hpI, qSolutionJet_mem_domain hpU hxx⟩

def nextTaylorCoefficient (g : MetricField) (a : ℝ) (P : Coord → ℝ)
    (n : ℕ) (x : ℝ) : ℝ :=
  -verticalJet (qResidual g P) n ![x, a]

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

def taylorApproximation (g : MetricField) (a : ℝ) (u0 u1 : ℝ → ℝ) : ℕ → Coord → ℝ
  | 0 => linearCauchy a u0 u1
  | n + 1 => fun p => taylorApproximation g a u0 u1 n p +
      taylorCorrection (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) a n p

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorCauchyData
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Weighted

theorem heightCauchyValue_contDiffOn {z : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (hz : ContDiffOn ℝ ∞ z U) (a : ℝ)
    (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U) :
    ContDiffOn ℝ ∞ (heightCauchyValue z a) I :=
  hz.comp (initialPoint_contDiff a).contDiffOn hcut

theorem linearCauchy_height_initial_state {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (left right a : ℝ)
    (hcut : ∀ x ∈ Ioo left right, (![x, a] : Coord) ∈ U)
    {x : ℝ} (hx : x ∈ Ioo left right) :
    qSolutionJet (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a)) ![x, a] =
      qSolutionJet z ![x, a] := by
  have h0 := heightCauchyValue_contDiffOn hz a hcut
  have h1 := heightCauchyVelocity_contDiffOn hz hU a hcut
  have hlin := linearCauchy_contDiffOn h0 h1 a
  let V : Set Coord := U ∩ spatialStrip (Ioo left right)
  have hV : IsOpen V := hU.inter (spatialStrip_isOpen isOpen_Ioo)
  have hzV : ContDiffOn ℝ ∞ z V := hz.mono inter_subset_left
  have hlinV : ContDiffOn ℝ ∞
      (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a)) V :=
    hlin.mono inter_subset_right
  have hpoint (y : ℝ) : boxPoint y a = (![y, a] : Coord) := by
    ext i
    fin_cases i <;> simp [boxPoint]
  have hline : ∀ x ∈ Ioo left right, boxPoint x a ∈ V := by
    intro y hy
    rw [hpoint]
    exact ⟨hcut y hy, hy⟩
  have hval : ∀ y ∈ Ioo left right,
      linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a) (boxPoint y a) =
      z (boxPoint y a) := by
    intro y _
    rw [hpoint]
    exact linearCauchy_value a y _ _
  have hvel : ∀ y ∈ Ioo left right,
      coordPartial 1 (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a))
        (boxPoint y a) = coordPartial 1 z (boxPoint y a) := by
    intro y hy
    rw [hpoint]
    exact linearCauchy_velocity isOpen_Ioo h0 h1 a (p := ![y, a]) hy
  have hh := qSolutionJet_eq_of_cauchy_data hzV hlinV hV hline hval hvel hx
  rw [hpoint] at hh
  exact hh

theorem linearCauchy_height_initial_hessian {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (left right a : ℝ)
    (hcut : ∀ x ∈ Ioo left right, (![x, a] : Coord) ∈ U)
    {x : ℝ} (hx : x ∈ Ioo left right) :
    covHessian g (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a))
      ![x, a] 0 0 = covHessian g z ![x, a] 0 0 := by
  rw [← stateQDenominator_qSolutionJet,
    linearCauchy_height_initial_state hz hU left right a hcut hx,
    stateQDenominator_qSolutionJet]

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QReferenceInitialTolerance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Taylor

theorem exists_reference_XX_tolerance (B : ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ a b : QFirstInput,
      ‖a‖ ≤ B → d ≤ qFirstDet a → c ≤ |qFirstXX a| →
      ‖b - a‖ ≤ epsilon → c / 2 ≤ |qFirstXX b| := by
  obtain ⟨H, _, _, hH, _, _, hcompare⟩ := exists_uniform_qFirst_comparison B hd hc
  let D := 4 * max B 0 + 2
  have hD : 0 < D := by dsimp [D] <;> positivity
  let epsilon := min 1 (min (d / (2 * D)) (c / (2 * (H + 1))))
  have he : 0 < epsilon := by dsimp [epsilon] <;> positivity
  refine ⟨epsilon, he, ?_⟩
  intro a b ha hdet hxx hdist
  have he1 : epsilon ≤ 1 := min_le_left _ _
  have hed : epsilon ≤ d / (2 * D) := (min_le_right _ _).trans (min_le_left _ _)
  have hec : epsilon ≤ c / (2 * (H + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hdist0 : 0 ≤ ‖b - a‖ := norm_nonneg _
  have hdsmall : D * ‖b - a‖ ≤ d / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * D by positivity)).mp (hdist.trans hed)
    nlinarith
  have hcsmall : H * ‖b - a‖ ≤ c / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * (H + 1) by positivity)).mp (hdist.trans hec)
    nlinarith
  exact (hcompare a b ha hdet hxx (hdist.trans he1) hdsmall hcsmall).1 b
    (right_mem_segment ℝ a b)

theorem exists_actual_reference_XX_tolerance (G W : ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (g h : MetricField) (w : DarbouxState),
      ‖actualCurvatureFirstInput g (statePoint w)‖ ≤ G → ‖w‖ ≤ W →
      d ≤ (g (statePoint w)).det → c ≤ |stateQDenominator g w| →
      ‖actualCurvatureFirstInput h (statePoint w) - actualCurvatureFirstInput g (statePoint w)‖ ≤ epsilon →
      c / 2 ≤ |stateQDenominator h w| := by
  obtain ⟨epsilon, he, htol⟩ := exists_reference_XX_tolerance (max G W) hd hc
  refine ⟨epsilon, he, ?_⟩
  intro g h w hg hw hdet hxx hdist
  have ha : ‖qFirstBundle g w‖ ≤ max G W := by
    change max ‖actualCurvatureFirstInput g (statePoint w)‖ ‖w‖ ≤ max G W
    exact max_le_max hg hw
  exact htol (qFirstBundle g w) (qFirstBundle h w) ha hdet hxx
    (by simpa only [qFirstBundle_distance] using hdist)

theorem exists_reference_linearCauchy_XX_tolerance (G W : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (g h : MetricField) (z : Coord → ℝ) (U : Set Coord),
      ContDiffOn ℝ ∞ z U → IsOpen U → ∀ left right a : ℝ,
      (∀ x ∈ Ioo left right, (![x, a] : Coord) ∈ U) →
      ∀ x ∈ Ioo left right,
      ‖actualCurvatureFirstInput g ![x, a]‖ ≤ G → ‖qSolutionJet z ![x, a]‖ ≤ W →
      d ≤ (g ![x, a]).det → c ≤ |covHessian g z ![x, a] 0 0| →
      ‖actualCurvatureFirstInput h ![x, a] - actualCurvatureFirstInput g ![x, a]‖ ≤ epsilon →
      c / 2 ≤ |covHessian h (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a))
        ![x, a] 0 0| := by
  obtain ⟨epsilon, he, htol⟩ := exists_actual_reference_XX_tolerance G W hd hc
  refine ⟨epsilon, he, ?_⟩
  intro g h z U hz hU left right a hcut x hx hg hw hdet hxx hdist
  rw [linearCauchy_height_initial_hessian hz hU left right a hcut hx]
  have hb := htol g h (qSolutionJet z ![x, a])
    (by simpa only [statePoint_qSolutionJet] using hg) hw
    (by simpa only [statePoint_qSolutionJet] using hdet)
    (by simpa only [stateQDenominator_qSolutionJet] using hxx)
    (by simpa only [statePoint_qSolutionJet] using hdist)
  simpa only [stateQDenominator_qSolutionJet] using hb

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_BoundedClassInitialJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Flow SmoothLocal.Perturbation

theorem actual_first_input_norm_le {g : MetricField} {p : Coord} {G : ℝ} (hG : 0 ≤ G)
    (hvalue : ∀ i j, |g p i j| ≤ G)
    (hpartial : ∀ a i j, |coordPartial a (fun q => g q i j) p| ≤ G) :
    ‖actualCurvatureFirstInput g p‖ ≤ G := by
  change max ‖(fun i j => g p i j)‖
    ‖(fun a i j => coordPartial a (fun q => g q i j) p)‖ ≤ G
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro j
    exact hvalue i j
  · apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro j
    exact hpartial a i j

theorem sheared_first_input_norm_le_of_original_jets
    {g : MetricField} {U : Set Coord} {p : Coord} {q0 G : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : inverseShearCoordinates q0 p ∈ U)
    (hG : 0 ≤ G) (hq0 : |q0| ≤ 1)
    (hgB : ∀ i j k, k ≤ 1 →
      ‖iteratedFDeriv ℝ k (fun a => g a i j) (inverseShearCoordinates q0 p)‖ ≤ G) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates g q0) p‖ ≤ 8 * G := by
  have hf : ‖actualCurvatureFirstInput g (inverseShearCoordinates q0 p)‖ ≤ G := by
    apply actual_first_input_norm_le hG
    · intro i j
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hgB i j 0 (by omega)
    · intro a i j
      exact (norm_iteratedCoordPartial_le_jet (hg.1 i j) hU [a] hp).trans
        (hgB i j 1 (by omega))
  have hp' : affineCoordinates 0 (inverseShearMatrix q0) p ∈ U := by
    simpa only [← inverseShearCoordinates_eq_affine] using hp
  unfold metricInShearCoordinates
  rw [actualCurvatureFirstInput_affinePullback hg hU 0 (inverseShearMatrix q0) p hp']
  exact affineFirstJetMap_norm_le_eight _ (inverseShearMatrix_entry_le_one hq0) _ hG
    (by simpa only [← inverseShearCoordinates_eq_affine] using hf)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_ShearMetricFullJets
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem metricInShearCoordinates_sub (g h : MetricField) (q0 : ℝ) :
    metricInShearCoordinates (fun p => g p-h p) q0 =
      fun p => metricInShearCoordinates g q0 p-metricInShearCoordinates h q0 p := by
  funext p
  ext i j
  simp only [metricInShearCoordinates,affinePullbackMetric,Matrix.mul_apply,
    Matrix.transpose_apply,Matrix.sub_apply,Fin.sum_univ_two]
  ring

theorem sheared_metric_full_jet_bound {g : MetricField} {U : Set Coord}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun p => g p i j) U) (hU : IsOpen U)
    {q0 B : ℝ} (hq0 : |q0| ≤ 1) (hB : 0 ≤ B) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U) (n : ℕ)
    (hjet : ∀ i j, ‖iteratedFDeriv ℝ n (fun q => g q i j) (inverseShearCoordinates q0 p)‖ ≤ B)
    (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun q => metricInShearCoordinates g q0 q i j) p‖ ≤ 4*2^n*B := by
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  let c (a b : Fin 2) := inverseShearMatrix q0 a i*inverseShearMatrix q0 b j
  let f (a b : Fin 2) := heightInShearCoordinates (fun q => g q a b) q0
  let term (a b : Fin 2) : Coord → ℝ := fun q => c a b*f a b q
  have hfs (a b : Fin 2) : ContDiffOn ℝ ∞ (f a b) V :=
    heightInShearCoordinates_contDiffOn (hg a b) q0
  have hts (a b : Fin 2) : ContDiffAt ℝ n (term a b) p :=
    ((contDiffOn_const.mul (hfs a b)).contDiffAt (hV.mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hc (a b : Fin 2) : |c a b| ≤ 1 := by
    dsimp only [c]
    rw [abs_mul]
    exact (mul_le_mul (inverseShearMatrix_entry_le_one hq0 a i)
      (inverseShearMatrix_entry_le_one hq0 b j) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hnormL : ‖inverseShearCLM q0‖ ≤ 2 := (inverseShearCLM_norm_le q0).trans (by linarith)
  have htB (a b : Fin 2) : ‖iteratedFDeriv ℝ n (term a b) p‖ ≤ B*2^n := by
    have hchain := local_linear_full_jet_norm_bound (hg a b) hU (inverseShearCLM q0) hp n
    have hfB : ‖iteratedFDeriv ℝ n (f a b) p‖ ≤ B*2^n := by
      exact hchain.trans (mul_le_mul (hjet a b)
        (pow_le_pow_left₀ (norm_nonneg _) hnormL n) (pow_nonneg (norm_nonneg _) n) hB)
    change ‖iteratedFDeriv ℝ n ((c a b) • f a b) p‖ ≤ B*2^n
    rw [iteratedFDeriv_const_smul_apply
      (((hfs a b).contDiffAt (hV.mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top)),norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (hc a b) hfB (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  rw [metricInShearCoordinates_four_terms]
  change ‖iteratedFDeriv ℝ n ((term 0 0+term 0 1)+(term 1 0+term 1 1)) p‖ ≤ _
  rw [iteratedFDeriv_add_apply (f := term 0 0+term 0 1) (g := term 1 0+term 1 1)
      ((hts 0 0).add (hts 0 1)) ((hts 1 0).add (hts 1 1)),
    iteratedFDeriv_add_apply (hts 0 0) (hts 0 1),iteratedFDeriv_add_apply (hts 1 0) (hts 1 1)]
  calc
    _ ≤ (B*2^n+B*2^n)+(B*2^n+B*2^n) := (norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add (htB 0 0) (htB 0 1)))
        ((norm_add_le _ _).trans (add_le_add (htB 1 0) (htB 1 1))))
    _ = _ := by ring

theorem sheared_metric_full_jet_difference_le {g h : MetricField} {U : Set Coord}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun p => g p i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun p => h p i j) U) (hU : IsOpen U)
    {q0 epsilon : ℝ} (hq0 : |q0| ≤ 1) (he : 0 ≤ epsilon) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U) (n : ℕ)
    (hjet : ∀ i j, ‖iteratedFDeriv ℝ n (fun q => g q i j-h q i j)
      (inverseShearCoordinates q0 p)‖ ≤ epsilon) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun q => metricInShearCoordinates g q0 q i j-
      metricInShearCoordinates h q0 q i j) p‖ ≤ 4*2^n*epsilon := by
  have hb := sheared_metric_full_jet_bound
    (g := fun q => g q-h q) (fun a b => (hg a b).sub (hh a b)) hU hq0 he hp n hjet i j
  simpa only [metricInShearCoordinates_sub,Matrix.sub_apply] using hb

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_PulseCapSeparation
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
open SmoothLocal.HighEquation

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem testMetric_eventuallyEq_on_lower_cap
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {M q0 L r a delta tau : ℝ} (hM : 0 ≤ M) (hL : 0 < L) (hr : 0 < r)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    (hq0 : |q0| ≤ 1/20) (hcenter : |q 0-q0| ≤ 1/(100*L))
    (hT : L*r < 2) (ha : 0 < a) (haL : a ≤ L*r)
    (hrsmall : M*(r+107*(L*r)/100) ≤ 9/(100*L))
    (hd : 0 < delta) (ht : 0 < tau) (hwidth : delta/(2*tau) ≤ r/4)
    (gStar : MetricField) (N : ℕ) (R : LowerCapRectangle (-r/2))
    {p : Coord} (hp : p ∈ R.image Y) :
    testMetric gStar q0 a N delta tau =ᶠ[𝓝 p] gStar := by
  obtain ⟨v,hv,rfl⟩ := hp
  have hseed : r/2 ≤ |v 1| := by
    have htop : v 1 ≤ R.top := hv.2.2
    have hceil := R.top_lt
    have habs := neg_le_abs (v 1)
    linarith
  exact metric_add_eventuallyEq_of_not_mem_tsupport gStar (pulseTensor q0 a N delta tau)
    (pulseTensor_not_tsupport_exterior_seed hq hU hSU hY hrange hstart hode hsmall hM hL hr
      hpartial hq0 hcenter hT ha haL hrsmall hd ht hwidth N (R.region_subset_domain hv) hseed)

end SmoothLocal.Pulse

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

theorem reflectedMetric_sub (g h : MetricField) :
    reflectedMetric (g-h) = reflectedMetric g-reflectedMetric h := by
  funext p
  ext i j
  simp only [reflectedMetric_entry, Pi.sub_apply, Matrix.sub_apply]
  split_ifs <;> ring

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_QPointwiseCauchyJets
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

theorem cauchyVelocity_iteratedDeriv {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) {x t : ℝ}
    (hp : coordinatePoint x t ∈ U) (n : ℕ) :
    iteratedDeriv n (heightCauchyVelocity z t) x =
      spatialJet (spatialFirstJet z 1) n (coordinatePoint x t) := by
  have he : heightCauchyVelocity z t = (fun y => coordPartial 1 z (coordinatePoint y t)) := by
    funext y
    rw [coordinatePoint_eq_vector]
    rfl
  rw [he, horizontalJet_slice hU (partial_contDiffOn hz hU 1) t n x hp,
    horizontalJet_eq_spatialJet]
  rfl

theorem cauchyValue_iteratedDeriv_succ {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) {x t : ℝ}
    (hp : coordinatePoint x t ∈ U) (n : ℕ) :
    iteratedDeriv (n+1) (heightCauchyValue z t) x =
      spatialJet (spatialFirstJet z 0) n (coordinatePoint x t) := by
  have he : heightCauchyValue z t = (fun y => z (coordinatePoint y t)) := by
    funext y
    rw [coordinatePoint_eq_vector]
    rfl
  rw [he, horizontalJet_slice hU hz t (n+1) x hp]
  change coordPartial 0 (horizontalJet z n) (coordinatePoint x t) = _
  rw [← horizontalJet_coordPartial hU hz 0 n _ hp, horizontalJet_eq_spatialJet]
  rfl

theorem cauchy_fullJets_of_actual_spatial_firstJets
    {z : Coord → ℝ} {U : Set Coord} (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {x t : ℝ} (hp : coordinatePoint x t ∈ U) {N : ℕ} {Z B : ℝ}
    (hvalue : |z (coordinatePoint x t)| ≤ Z)
    (hspatial : ∀ i : Fin 2, ∀ n ≤ N,
      |spatialJet (spatialFirstJet z i) n (coordinatePoint x t)| ≤ B) :
    ∀ n ≤ N,
      ‖iteratedFDeriv ℝ n (heightCauchyValue z t) x‖ ≤ max Z B ∧
      ‖iteratedFDeriv ℝ n (heightCauchyVelocity z t) x‖ ≤ max Z B := by
  intro n hn
  constructor
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    cases n with
    | zero =>
      change |z ![x,t]| ≤ _
      rw [← coordinatePoint_eq_vector]
      exact hvalue.trans (le_max_left _ _)
    | succ n =>
      rw [cauchyValue_iteratedDeriv_succ hz hU hp n]
      exact (hspatial 0 n (by omega)).trans (le_max_right _ _)
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      cauchyVelocity_iteratedDeriv hz hU hp n]
    exact (hspatial 1 n hn).trans (le_max_right _ _)

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ForcingCoefficientSign
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

theorem forcingCoefficient_floor_of_reference_margins
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U)
    {e c D C : ℝ} (he : 0 < e) (hc : 0 < c)
    (hE : e ≤ heightEnergy g z p) (hdet : (g p).det ≤ D)
    (hxx : c ≤ |covHessian g z p 0 0|) (hxxup : |covHessian g z p 0 0| ≤ C) :
    forcingFloor e D C ≤ |forcingCoefficient g z p| := by
  exact (forcingCoefficient_bounds hg hp he (hg.2 p hp).det_pos hc hE le_rfl le_rfl
    (hdet.trans (le_max_left _ _)) hxx (hxxup.trans (le_max_left _ _))).2.1

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

structure QPulsePointBounds (gStar gTau : MetricField) (z : Coord → ℝ)
    (U : Set Coord) (q0 a delta tau : ℝ) (N : ℕ)
    (B Bcompare BQ D A d dcompare c epsilon epsilonQ : ℝ) (p : Coord) : Prop where
  point_mem : inverseShearCoordinates q0 p ∈ U
  referenceFirst : ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤ B
  referenceDet : d ≤ (metricInShearCoordinates gStar q0 p).det
  testFirst : ‖actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
    (inverseShearCoordinates q0 p)‖ ≤ Bcompare
  testDet : dcompare ≤ (testMetric gStar q0 a N delta tau (inverseShearCoordinates q0 p)).det
  approximationFirst : ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
    actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
      (inverseShearCoordinates q0 p)‖ ≤ epsilon
  approximationSecond : ∀ i j k l : Fin 2,
    |coordPartial i (coordPartial j (fun q => gTau q k l)) (inverseShearCoordinates q0 p)-
      coordPartial i (coordPartial j (fun q => testMetric gStar q0 a N delta tau q k l))
        (inverseShearCoordinates q0 p)| ≤ epsilon
  referenceState : ‖qFirstBundle (metricInShearCoordinates gStar q0)
    (qSolutionJet (heightInShearCoordinates z q0) p)‖ ≤ BQ
  referenceXX : c ≤ |covHessian (metricInShearCoordinates gStar q0)
    (heightInShearCoordinates z q0) p 0 0|
  baseFirstDistance : ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
    actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤ epsilonQ
  actualDensity : |curvatureDensity gTau (inverseShearCoordinates q0 p)| ≤ D
  referenceCoefficient : |forcingCoefficient (metricInShearCoordinates gStar q0)
    (heightInShearCoordinates z q0) p| ≤ A

def actualShearedQForcing (gStar gTau : MetricField) (z : Coord → ℝ) (q0 : ℝ) (p : Coord) : ℝ :=
  sixVariableQ (metricInShearCoordinates gTau q0) (qSolutionJet (heightInShearCoordinates z q0) p)-
    sixVariableQ (metricInShearCoordinates gStar q0) (qSolutionJet (heightInShearCoordinates z q0) p)

def actualShearedQLeading (gStar : MetricField) (z : Coord → ℝ)
    (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) : ℝ :=
  2*forcingCoefficient (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p*
    pulsePrincipalLeading a N delta tau p

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_QPulseFirstJetBudget
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def qPulseFirstJetBudget (a : ℝ) (ha : 0 < a) (N : ℕ) (delta tau : ℝ) : ℝ :=
  (8+scalarPulseFirstJetBound a ha delta)*tau/tau^N

theorem qPulseFirstJetBudget_nonneg {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 0 ≤ tau) : 0 ≤ qPulseFirstJetBudget a ha N delta tau :=
  div_nonneg (mul_nonneg (by linarith [scalarPulseFirstJetBound_nonneg ha delta]) ht)
    (pow_nonneg ht N)

theorem actual_sheared_first_jet_error_nat
    {gStar gTau : MetricField} {U : Set Coord} {q0 a delta : ℝ} {N n : ℕ}
    (hgStar : SmoothPositiveOn gStar U)
    (hgTest : SmoothPositiveOn (testMetric gStar q0 a N delta n) U)
    (hgTau : SmoothPositiveOn gTau U) (hU : IsOpen U)
    (hq : |q0| ≤ 1) (ha : 0 < a) (hN : 0 < N) (hn : 1 ≤ n) (hlarge : N-1 ≤ n)
    {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hjet : ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
      actualCurvatureFirstInput (testMetric gStar q0 a N delta n)
        (inverseShearCoordinates q0 p)‖ ≤ 1/(n : ℝ)^n) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
      actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤
      qPulseFirstJetBudget a ha N delta n := by
  have ht : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfirst := actual_sheared_solution_first_jet_error hgStar hgTest hgTau hU hq ha ht hp hjet
  calc
    _ ≤ 8*(1/(n : ℝ)^n)+scalarPulseFirstJetBudget a ha N delta n := hfirst
    _ ≤ 8*((n : ℝ)/(n : ℝ)^N)+scalarPulseFirstJetBudget a ha N delta n :=
      add_le_add (mul_le_mul_of_nonneg_left
        (approximation_budget_le_pulse_error hN hn hlarge) (by norm_num : (0 : ℝ) ≤ 8)) le_rfl
    _ = _ := by unfold qPulseFirstJetBudget scalarPulseFirstJetBudget; ring

theorem qPulseFirstJetBudget_tendsto_zero {a : ℝ} (ha : 0 < a) (N : ℕ)
    (hN : 1 < N) (delta : ℝ) :
    Tendsto (qPulseFirstJetBudget a ha N delta) atTop (𝓝 0) := by
  have hn : N-1 ≠ 0 := by omega
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).pow (N-1)
  have h : Tendsto (fun t : ℝ => (8+scalarPulseFirstJetBound a ha delta)*(t⁻¹)^(N-1))
      atTop (𝓝 0) := by
    simpa only [zero_pow hn,mul_zero] using hi.const_mul (8+scalarPulseFirstJetBound a ha delta)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hN' : N = 1+(N-1) := by omega
  have hr : t/t^N = (t⁻¹)^(N-1) := by
    conv_lhs => rw [hN',pow_add,pow_one]
    rw [inv_pow]
    field_simp [ht.ne']
  simp only [qPulseFirstJetBudget,mul_div_assoc,hr]

theorem qPulseFirstJetBudget_eventual_margins (B H : ℝ) {d c a : ℝ}
    (hd : 0 < d) (hc : 0 < c) (ha : 0 < a) (N : ℕ) (hN : 1 < N)
    (delta : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ tau : ℝ, T ≤ tau →
      qPulseFirstJetBudget a ha N delta tau ≤ 1 ∧
      (4*max B 0+2)*qPulseFirstJetBudget a ha N delta tau ≤ d/2 ∧
      H*qPulseFirstJetBudget a ha N delta tau ≤ c/2 := by
  have htend := qPulseFirstJetBudget_tendsto_zero ha N hN delta
  have h1 : ∀ᶠ t : ℝ in atTop, qPulseFirstJetBudget a ha N delta t < 1 :=
    htend.eventually (eventually_lt_nhds zero_lt_one)
  have hd' : Tendsto (fun t : ℝ => (4*max B 0+2)*qPulseFirstJetBudget a ha N delta t)
      atTop (𝓝 0) := by simpa only [mul_zero] using htend.const_mul (4*max B 0+2)
  have hc' : Tendsto (fun t : ℝ => H*qPulseFirstJetBudget a ha N delta t)
      atTop (𝓝 0) := by simpa only [mul_zero] using htend.const_mul H
  have hev : ∀ᶠ t : ℝ in atTop,
      qPulseFirstJetBudget a ha N delta t ≤ 1 ∧
      (4*max B 0+2)*qPulseFirstJetBudget a ha N delta t ≤ d/2 ∧
      H*qPulseFirstJetBudget a ha N delta t ≤ c/2 := by
    filter_upwards [h1,hd'.eventually (eventually_lt_nhds (half_pos hd)),
      hc'.eventually (eventually_lt_nhds (half_pos hc))] with t ht1 htd htc
    exact ⟨ht1.le,htd.le,htc.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.mp hev
  exact ⟨max T 1,le_max_right _ _,fun t ht => hT t ((le_max_left _ _).trans ht)⟩

end SmoothLocal.Pulse

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

def actualComparisonSource (gStar gTau : MetricField) (z : Coord → ℝ)
    (q0 : ℝ) (P : Coord → ℝ) (p : Coord) : ℝ :=
  actualShearedQForcing gStar gTau z q0 p -
    qResidual (metricInShearCoordinates gStar q0) P p

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem comparison_segment_direction_bound
    {P z : Coord → ℝ} {U T : Set Coord} {Z0 Z sigma : ℝ}
    (hU : IsOpen U) (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hTU : T ⊆ U) (hPZ : CoordinateBound P T 3 Z0) (hzZ : CoordinateBound z T 3 Z)
    {p : Coord} (hp : p ∈ T) (hs : sigma ∈ Icc (0 : ℝ) 1) (j : Fin 2) :
    ‖(1-sigma) • coordPartial j (qSolutionJet P) p +
      sigma • coordPartial j (qSolutionJet z) p‖ ≤ max 1 Z0 + max 1 Z := by
  have h0 := coordPartial_qSolutionJet_norm_bound hU hP hTU hPZ hp j
  have h1 := coordPartial_qSolutionJet_norm_bound hU hz hTU hzZ hp j
  calc
    _ ≤ ‖(1-sigma) • coordPartial j (qSolutionJet P) p‖ +
        ‖sigma • coordPartial j (qSolutionJet z) p‖ := norm_add_le _ _
    _ = (1-sigma)*‖coordPartial j (qSolutionJet P) p‖ +
        sigma*‖coordPartial j (qSolutionJet z) p‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hs.2),abs_of_nonneg hs.1]
    _ ≤ (1-sigma)*max 1 Z0 + sigma*max 1 Z :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hs.2))
        (mul_le_mul_of_nonneg_left h1 hs.1)
    _ ≤ max 1 Z0 + max 1 Z := by
      have hn0 : 0 ≤ max 1 Z0 := zero_le_one.trans (le_max_left _ _)
      have hn1 : 0 ≤ max 1 Z := zero_le_one.trans (le_max_left _ _)
      exact add_le_add (mul_le_of_le_one_left hn0 (by linarith [hs.1]))
        (mul_le_of_le_one_left hn1 hs.2)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualComparisonEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Taylor

def metricComparisonSource (g gRef : MetricField) (P z : Coord → ℝ) (p : Coord) : ℝ :=
  sixVariableQ g (qSolutionJet z p)-sixVariableQ gRef (qSolutionJet z p)-qResidual gRef P p

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_QMetricApproximationInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem iteratedCoordPartial_sub_actual {f h : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (ds : List (Fin 2)) {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds (fun q => f q-h q) p =
      iteratedCoordPartial ds f p-iteratedCoordPartial ds h p := by
  rw [iteratedCoordPartial_eq_jet (hf.sub hh) hU ds hp]
  change iteratedFDeriv ℝ ds.length (f-h) p (coordinateDirections ds) = _
  rw [iteratedFDeriv_sub_apply (i := ds.length)
    ((hf.contDiffAt (hU.mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top))
    ((hh.contDiffAt (hU.mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top)),
    sub_apply,
    ←iteratedCoordPartial_eq_jet hf hU ds hp,←iteratedCoordPartial_eq_jet hh hU ds hp]

theorem actual_metric_word_difference_le {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j : Fin 2) (ds : List (Fin 2)) {epsilon : ℝ}
    (hjet : ‖iteratedFDeriv ℝ ds.length (fun q => g q i j-h q i j) p‖ ≤ epsilon) :
    |iteratedCoordPartial ds (fun q => g q i j) p-
      iteratedCoordPartial ds (fun q => h q i j) p| ≤ epsilon := by
  have hb := (norm_iteratedCoordPartial_le_jet ((hg.1 i j).sub (hh.1 i j)) hU ds hp).trans hjet
  rw [iteratedCoordPartial_sub_actual (hg.1 i j) (hh.1 i j) hU ds hp,
    Real.norm_eq_abs] at hb
  exact hb

theorem actual_metric_jet_approximation_inputs {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {epsilon : ℝ}
    (hjets : ∀ i j : Fin 2, ∀ k ≤ 2,
      ‖iteratedFDeriv ℝ k (fun q => g q i j-h q i j) p‖ ≤ epsilon) :
    ‖actualCurvatureFirstInput g p-actualCurvatureFirstInput h p‖ ≤ epsilon ∧
      ∀ i j k l : Fin 2,
        |coordPartial i (coordPartial j (fun q => g q k l)) p-
          coordPartial i (coordPartial j (fun q => h q k l)) p| ≤ epsilon := by
  have he : 0 ≤ epsilon := (norm_nonneg _).trans (hjets 0 0 0 (by omega))
  have hval (i j : Fin 2) : |g p i j-h p i j| ≤ epsilon := by
    simpa only [iteratedCoordPartial] using actual_metric_word_difference_le hg hh hU hp i j []
      (hjets i j 0 (by omega))
  have hder (d i j : Fin 2) :
      |coordPartial d (fun q => g q i j) p-coordPartial d (fun q => h q i j) p| ≤ epsilon := by
    simpa only [iteratedCoordPartial] using actual_metric_word_difference_le hg hh hU hp i j [d]
      (hjets i j 1 (by omega))
  constructor
  · change max ‖(fun i j => g p i j-h p i j)‖
      ‖(fun d i j => coordPartial d (fun q => g q i j) p-
        coordPartial d (fun q => h q i j) p)‖ ≤ epsilon
    apply max_le
    · apply (pi_norm_le_iff_of_nonneg he).mpr
      intro i
      apply (pi_norm_le_iff_of_nonneg he).mpr
      intro j
      simpa only [Real.norm_eq_abs] using hval i j
    · apply (pi_norm_le_iff_of_nonneg he).mpr
      intro d
      apply (pi_norm_le_iff_of_nonneg he).mpr
      intro i
      apply (pi_norm_le_iff_of_nonneg he).mpr
      intro j
      simpa only [Real.norm_eq_abs] using hder d i j
  · intro i j k l
    simpa only [iteratedCoordPartial] using actual_metric_word_difference_le hg hh hU hp k l [i,j]
      (hjets k l 2 (by omega))

theorem actual_sheared_first_jet_error_from_Ctau
    {gStar gTau : MetricField} {U : Set Coord} {q0 a delta : ℝ} {N n : ℕ}
    (hgStar : SmoothPositiveOn gStar U)
    (hgTest : SmoothPositiveOn (testMetric gStar q0 a N delta n) U)
    (hgTau : SmoothPositiveOn gTau U) (hU : IsOpen U)
    (hq : |q0| ≤ 1) (ha : 0 < a) (hN : 0 < N) (hn : 2 ≤ n) (hlarge : N-1 ≤ n)
    {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hjets : ∀ i j : Fin 2, ∀ k ≤ n,
      ‖iteratedFDeriv ℝ k (fun q => gTau q i j-testMetric gStar q0 a N delta n q i j)
        (inverseShearCoordinates q0 p)‖ ≤ 1/(n : ℝ)^n) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
      actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤
      qPulseFirstJetBudget a ha N delta n := by
  apply actual_sheared_first_jet_error_nat hgStar hgTest hgTau hU hq ha hN
    (by omega) hlarge hp
  exact (actual_metric_jet_approximation_inputs hgTau hgTest hU hp
    (fun i j k hk => hjets i j k (hk.trans hn))).1

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QClosedStripMargins
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
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem qSolutionJet_distance_on_closed_strip {z z0 : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hz0 : ContDiffOn ℝ ∞ z0 U) (hU : IsOpen U)
    {left right a b x t : ℝ}
    (hbox : closedRectangle left right a b ⊆ U)
    (hx : x ∈ Icc left right) (hab : a ≤ b) (ht : t ∈ Icc a b)
    {M M0 : ℝ} (hM : 0 ≤ M) (hM0 : 0 ≤ M0)
    (hB : CoordinateBound z (closedRectangle left right a b) 3 M)
    (hB0 : CoordinateBound z0 (closedRectangle left right a b) 3 M0)
    (hinitial : qSolutionJet z0 (boxPoint x a) = qSolutionJet z (boxPoint x a)) :
    ‖qSolutionJet z0 (boxPoint x t)-qSolutionJet z (boxPoint x t)‖ ≤ (M+M0)*(b-a) := by
  have hword (ds : List (Fin 2)) (hds : ds.length ≤ 2)
      (he : iteratedCoordPartial ds z0 (boxPoint x a) = iteratedCoordPartial ds z (boxPoint x a)) :
      |iteratedCoordPartial ds z0 (boxPoint x t)-iteratedCoordPartial ds z (boxPoint x t)| ≤
        (M+M0)*(b-a) := by
    apply (coordinate_word_difference_on_strip hz hz0 hU hbox hx hab ht hB hB0 ds hds he).trans
    apply mul_le_mul_of_nonneg_left _ (add_nonneg hM hM0)
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  apply state_distance_le_of_coordinate_error (mul_nonneg (add_nonneg hM hM0) (sub_nonneg.mpr hab))
  apply qSolutionJet_coordinate_error z z0 (boxPoint x t)
    (mul_nonneg (add_nonneg hM hM0) (sub_nonneg.mpr hab))
  · intro i
    fin_cases i
    · exact hword [0] (by norm_num) (congrFun hinitial 2)
    · exact hword [1] (by norm_num) (congrFun hinitial 3)
  · exact hword [0,1] (by norm_num) (congrFun hinitial 4)
  · exact hword [0,0] (by norm_num) (congrFun hinitial 5)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseSpatialParts
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem pulse_spatial_flux_partial (i : Fin 2) {a tau : ℝ}
    {S v : Coord → ℝ} {U : Set Coord}
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) :
    coordPartial 0 (fun q => pulseSpatialTest a tau q*S q*coordPartial i v q) p =
      deriv (pulseTest a tau) (p 0)*S p*coordPartial i v p+
      pulseSpatialTest a tau p*coordPartial 0 S p*coordPartial i v p+
      pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial i v) p := by
  have hψ := (pulseSpatialTest_contDiff a tau).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p
  have hSd := (hS.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hvid := ((partial_contDiffOn hv hU i).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have houter := HessianCalculus.coordPartial_mul_at (hψ.mul hSd) hvid 0
  dsimp only [Pi.mul_apply] at houter
  have hinner := HessianCalculus.coordPartial_mul_at hψ hSd 0
  change coordPartial 0 (pulseSpatialTest a tau * S) p = _ at hinner
  rw [houter,hinner,pulseSpatialTest_partial]
  ring

theorem pulse_spatial_second_parts (i : Fin 2) {a delta tau : ℝ}
    {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U)
    (hSU : pulseStrip a delta tau ⊆ U) :
    rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial i v) p) =
      -rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => deriv (pulseTest a tau) (p 0)*S p*coordPartial i v p)-
       rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*coordPartial 0 S p*coordPartial i v p) := by
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hψ : ContDiffOn ℝ ∞ (pulseSpatialTest a tau) U := (pulseSpatialTest_contDiff a tau).contDiffOn
  have hψ' : ContDiffOn ℝ ∞ (fun p : Coord => deriv (pulseTest a tau) (p 0)) U :=
    ((contDiff_infty_iff_deriv.mp (pulseTest_contDiff a tau)).2.comp (contDiff_apply ℝ ℝ 0)).contDiffOn
  have hvi := partial_contDiffOn hv hU i
  have hflux : ContDiffOn ℝ ∞ (fun p => pulseSpatialTest a tau p*S p*coordPartial i v p) U :=
    (hψ.mul hS).mul hvi
  have hminus : axisBump a (-a) = 0 := axisBump_zero ha.le (by simp [abs_of_pos ha])
  have hplus : axisBump a a = 0 := axisBump_zero ha.le (by simp [abs_of_pos ha])
  have hedge : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      (pulseSpatialTest a tau (boxPoint (-a) theta)*S (boxPoint (-a) theta)*
        coordPartial i v (boxPoint (-a) theta)) = 0 ∧
      (pulseSpatialTest a tau (boxPoint a theta)*S (boxPoint a theta)*
        coordPartial i v (boxPoint a theta)) = 0 := by
    intro theta htheta
    simp only [pulseSpatialTest,pulseTest,pulse_boxPoint_zero,hminus,hplus,zero_mul,and_self]
  have hzero := rectangleIntegral_partial_t_zero hlr hbt hU hflux hSU hedge
  have heq := rectangleIntegral_congr hlr hbt
    (fun p hp => pulse_spatial_flux_partial i (a := a) (tau := tau) hS hv hU (hSU hp))
  rw [heq] at hzero
  have h1 := ((hψ'.mul hS).mul hvi).continuousOn.mono hSU
  have h2 := ((hψ.mul (partial_contDiffOn hS hU 0)).mul hvi).continuousOn.mono hSU
  have h3 := ((hψ.mul hS).mul (partial_contDiffOn hvi hU 0)).continuousOn.mono hSU
  rw [rectangleIntegral_add (f := fun p => deriv (pulseTest a tau) (p 0)*S p*coordPartial i v p+
      pulseSpatialTest a tau p*coordPartial 0 S p*coordPartial i v p)
      (g := fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial i v) p)
      hlr hbt (h1.add h2) h3,
    rectangleIntegral_add hlr hbt h1 h2] at hzero
  linarith

theorem pulse_spatial_second_cost (i : Fin 2) {a delta tau S0 S1 M : ℝ} {N : ℕ}
    {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hS0 : 0 ≤ S0) (hS1 : 0 ≤ S1) (hM : 0 ≤ M)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U)
    (hSU : pulseStrip a delta tau ⊆ U)
    (hSB : ∀ p ∈ pulseStrip a delta tau, |S p| ≤ S0)
    (hS1B : ∀ p ∈ pulseStrip a delta tau, |coordPartial 0 S p| ≤ S1)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ M*delta*tau/tau^N) :
    |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial i v) p)| ≤
      (2*pulseTestDerivativeBound a ha*S0*Real.sqrt (2*a)*M)*delta^2*tau/tau^N+
        (2*axisBumpDerivativeBound a ha 0*S1*Real.sqrt (2*a)*M)*delta^2/tau^N := by
  have htpos := zero_lt_one.trans_le ht
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd htpos.le]
  have hfirst := pulse_derivative_pairing_delta_sq i ha hd ht hS0 hM hU hSU hS hv hSB hL2
  have hsecond := pulse_test_pairing_extra_inv_tau i ha hd ht hS1 hM hU hSU
    (partial_contDiffOn hS hU 0) hv hS1B hL2
  have hfirst' : |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => deriv (pulseTest a tau) (p 0)*S p*coordPartial i v p)| ≤
      (2*pulseTestDerivativeBound a ha*S0*Real.sqrt (2*a)*M)*delta^2*tau/tau^N := by
    rw [rectangleIntegral_eq_Icc_slices _ hlr hbt]
    simpa only [pulse_boxPoint_zero] using hfirst
  have hsecond' : |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*coordPartial 0 S p*coordPartial i v p)| ≤
      (2*axisBumpDerivativeBound a ha 0*S1*Real.sqrt (2*a)*M)*delta^2/tau^N := by
    rw [rectangleIntegral_eq_Icc_slices _ hlr hbt]
    simpa only [pulseSpatialTest,pulse_boxPoint_zero] using hsecond
  rw [pulse_spatial_second_parts i ha hd htpos hS hv hU hSU]
  exact ((abs_sub _ _).trans (add_le_add (by simpa only [abs_neg] using hfirst') hsecond'))

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseTemporalParts
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem pulse_temporal_flux_partial {a tau : ℝ} {v : Coord → ℝ} {U : Set Coord}
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    coordPartial 1 (fun q => pulseSpatialTest a tau q*coordPartial 1 v q) p =
      pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p := by
  have hψ := (pulseSpatialTest_contDiff a tau).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p
  have hvt := ((partial_contDiffOn hv hU 1).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [HessianCalculus.coordPartial_mul_at hψ hvt 1,pulseSpatialTest_partial_time]
  ring

theorem pulse_temporal_second_parts {a delta tau : ℝ}
    {v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U) :
    rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p) =
      (∫ x in (-a)..a, pulseTest a tau x*coordPartial 1 v (boxPoint x (delta/tau))) -
        (∫ x in (-a)..a, pulseTest a tau x*coordPartial 1 v (boxPoint x (-(delta/tau)))) := by
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hflux : ContDiffOn ℝ ∞ (fun p => pulseSpatialTest a tau p*coordPartial 1 v p) U :=
    (pulseSpatialTest_contDiff a tau).contDiffOn.mul (partial_contDiffOn hv hU 1)
  have hFTC := rectangleIntegral_partial_time_boundary hlr hbt hU hflux hSU
  have heq := rectangleIntegral_congr hlr hbt
    (fun p hp => pulse_temporal_flux_partial (a := a) (tau := tau) hv hU (hSU hp))
  rw [heq] at hFTC
  simpa only [pulseSpatialTest,pulse_boxPoint_zero] using hFTC

theorem pulse_temporal_second_parts_zero_initial {a delta tau : ℝ}
    {v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hinitial : ∀ x ∈ Icc (-a) a, coordPartial 1 v (boxPoint x (-(delta/tau))) = 0) :
    rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p) =
      ∫ x in (-a)..a, pulseTest a tau x*coordPartial 1 v (boxPoint x (delta/tau)) := by
  rw [pulse_temporal_second_parts ha hd ht hv hU hSU]
  have hzero : (∫ x in (-a)..a, pulseTest a tau x*coordPartial 1 v (boxPoint x (-(delta/tau)))) = 0 := by
    calc
      _ = ∫ _x in (-a)..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        rw [hinitial x (by simpa only [uIcc_of_le (by linarith : -a ≤ a)] using hx),mul_zero]
      _ = 0 := intervalIntegral.integral_zero
  rw [hzero,sub_zero]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseTemporalMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Taylor

theorem pulse_temporal_moment_finite_bound {a B delta tau : ℝ}
    {v : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hd : 0 ≤ delta) (htau : 0 < tau)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hI : IsOpen I) (hsub : Icc (-a) a ⊆ I)
    (hupper : ∀ x ∈ I, (![x,delta/tau] : Coord) ∈ U)
    (hinitial : ∀ x ∈ Icc (-a) a, coordPartial 1 v (boxPoint x (-(delta/tau))) = 0)
    (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a,
      ‖iteratedFDeriv ℝ k (heightCauchyVelocity v (delta/tau)) x‖ ≤ B) :
    |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p)| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N := by
  rw [pulse_temporal_second_parts_zero_initial ha hd htau hv hU hSU hinitial]
  have hf := heightCauchyVelocity_contDiffOn hv hU (delta/tau) hupper
  have hb := pulse_test_interval_finite_bound ha hB htau hI hf hsub N hjet
  simpa only [heightCauchyVelocity,pulse_boxPoint_eq] using hb

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseOperatorMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor
open SmoothLocal.HighEquation

theorem testedOperatorSource_moment_identity {a delta tau : ℝ}
    {R S b c v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hR : ContDiffOn ℝ ∞ R U) (hS : ContDiffOn ℝ ∞ S U)
    (hb : ContDiffOn ℝ ∞ b U) (hc : ContDiffOn ℝ ∞ c U)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U) :
    pulseWeightedMoment a delta tau (testedOperatorSource R S b c v) =
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p)-
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*R p*coordPartial 0 (coordPartial 1 v) p)-
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial 0 v) p)-
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*b p*coordPartial 1 v p)-
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*c p*coordPartial 0 v p) := by
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hψ : ContinuousOn (pulseSpatialTest a tau) (pulseStrip a delta tau) :=
    (pulseSpatialTest_contDiff a tau).continuous.continuousOn
  have hvi (i : Fin 2) := (partial_contDiffOn hv hU i).continuousOn.mono hSU
  have hvij (i j : Fin 2) := (partial_contDiffOn (partial_contDiffOn hv hU j) hU i).continuousOn.mono hSU
  have h0 := hψ.mul (hvij 1 1)
  have h1 := (hψ.mul (hR.continuousOn.mono hSU)).mul (hvij 0 1)
  have h2 := (hψ.mul (hS.continuousOn.mono hSU)).mul (hvij 0 0)
  have h3 := (hψ.mul (hb.continuousOn.mono hSU)).mul (hvi 1)
  have h4 := (hψ.mul (hc.continuousOn.mono hSU)).mul (hvi 0)
  rw [pulseWeightedMoment_eq_tested_rectangle ha hd ht
    ((testedOperatorSource_contDiffOn hR hS hb hc hv hU).continuousOn.mono hSU)]
  have heq : (fun p => pulseSpatialTest a tau p*testedOperatorSource R S b c v p) =
      fun p => (((pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p-
        pulseSpatialTest a tau p*R p*coordPartial 0 (coordPartial 1 v) p)-
        pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial 0 v) p)-
        pulseSpatialTest a tau p*b p*coordPartial 1 v p)-
        pulseSpatialTest a tau p*c p*coordPartial 0 v p := by
    funext p
    unfold testedOperatorSource hyperbolicOperator
    ring
  have hs4 := rectangleIntegral_sub hlr hbt (((h0.sub h1).sub h2).sub h3) h4
  have hs3 := rectangleIntegral_sub hlr hbt ((h0.sub h1).sub h2) h3
  have hs2 := rectangleIntegral_sub hlr hbt (h0.sub h1) h2
  have hs1 := rectangleIntegral_sub hlr hbt h0 h1
  simp only [Pi.mul_def,Pi.sub_def] at hs4 hs3 hs2 hs1
  rw [heq,hs4,hs3,hs2,hs1]

theorem testedOperatorSource_moment_cost {a delta tau K K1 M B : ℝ} {N : ℕ}
    {R S b c v : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hK : 0 ≤ K) (hK1 : 0 ≤ K1) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hR : ContDiffOn ℝ ∞ R U) (hS : ContDiffOn ℝ ∞ S U)
    (hb : ContDiffOn ℝ ∞ b U) (hc : ContDiffOn ℝ ∞ c U)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hcoeff : ∀ p ∈ pulseStrip a delta tau, |R p| ≤ K ∧ |S p| ≤ K ∧ |b p| ≤ K ∧ |c p| ≤ K)
    (hderiv : ∀ p ∈ pulseStrip a delta tau, |coordPartial 0 R p| ≤ K1 ∧ |coordPartial 0 S p| ≤ K1)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau), ∀ i : Fin 2,
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ M*delta*tau/tau^N)
    (hI : IsOpen I) (hsub : Icc (-a) a ⊆ I)
    (hupper : ∀ x ∈ I, (![x,delta/tau] : Coord) ∈ U)
    (hinitial : ∀ x ∈ Icc (-a) a, coordPartial 1 v (boxPoint x (-(delta/tau))) = 0)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a,
      ‖iteratedFDeriv ℝ k (heightCauchyVelocity v (delta/tau)) x‖ ≤ B) :
    |pulseWeightedMoment a delta tau (testedOperatorSource R S b c v)| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N+
      (4*pulseTestDerivativeBound a ha*K*Real.sqrt (2*a)*M)*delta^2*tau/tau^N+
      (4*axisBumpDerivativeBound a ha 0*(K1+K)*Real.sqrt (2*a)*M)*delta^2/tau^N := by
  have htpos := zero_lt_one.trans_le ht
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd htpos.le]
  have htime := pulse_temporal_moment_finite_bound ha hB hd htpos hv hU hSU hI hsub hupper hinitial N hjet
  have hRcost := pulse_spatial_second_cost 1 ha hd ht hK hK1 hM hR hv hU hSU
    (fun p hp => (hcoeff p hp).1) (fun p hp => (hderiv p hp).1) (fun theta ht => hL2 theta ht 1)
  have hScost := pulse_spatial_second_cost 0 ha hd ht hK hK1 hM hS hv hU hSU
    (fun p hp => (hcoeff p hp).2.1) (fun p hp => (hderiv p hp).2) (fun theta ht => hL2 theta ht 0)
  have hbcost := pulse_test_pairing_extra_inv_tau 1 ha hd ht hK hM hU hSU hb hv
    (fun p hp => (hcoeff p hp).2.2.1) (fun theta ht => hL2 theta ht 1)
  have hccost := pulse_test_pairing_extra_inv_tau 0 ha hd ht hK hM hU hSU hc hv
    (fun p hp => (hcoeff p hp).2.2.2) (fun theta ht => hL2 theta ht 0)
  have hfirst (F : Coord → ℝ) (i : Fin 2) :
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*F p*coordPartial i v p) =
      ∫ theta in Icc (-(delta/tau)) (delta/tau), ∫ x in Icc (-a) a,
        pulseTest a tau x*F (boxPoint x theta)*coordPartial i v (boxPoint x theta) := by
    rw [rectangleIntegral_eq_Icc_slices _ hlr hbt]
    simp only [pulseSpatialTest,pulse_boxPoint_zero]
  rw [testedOperatorSource_moment_identity ha hd htpos hR hS hb hc hv hU hSU]
  rw [← hfirst b 1] at hbcost
  rw [← hfirst c 0] at hccost
  have htriangle (a0 a1 a2 a3 a4 : ℝ) :
      |(((a0-a1)-a2)-a3)-a4| ≤ (((|a0|+|a1|)+|a2|)+|a3|)+|a4| := by
    have h01 := abs_sub a0 a1
    have h02 := (abs_sub (a0-a1) a2).trans (add_le_add h01 le_rfl)
    have h03 := (abs_sub ((a0-a1)-a2) a3).trans (add_le_add h02 le_rfl)
    exact (abs_sub (((a0-a1)-a2)-a3) a4).trans (add_le_add h03 le_rfl)
  calc
    _ ≤ (((|rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p)|+
      |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*R p*coordPartial 0 (coordPartial 1 v) p)|)+
      |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial 0 v) p)|)+
      |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*b p*coordPartial 1 v p)|)+
      |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*c p*coordPartial 0 v p)| := by
      exact htriangle _ _ _ _ _
    _ ≤ _ := by
      have hsum := add_le_add (add_le_add (add_le_add (add_le_add htime hRcost) hScost) hbcost) hccost
      apply hsum.trans_eq
      ring

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

theorem shearedModelSquare_eq_image (q0 : ℝ) :
    shearedModelSquare q0 = shearCoordinates q0 '' modelSquare := by
  ext p
  constructor
  · intro hp
    exact ⟨inverseShearCoordinates q0 p, hp, shear_inverse q0 p⟩
  · rintro ⟨x,hx,rfl⟩
    simpa only [shearedModelSquare, mem_preimage, inverse_shear] using hx

theorem shearedModelSquare_isCompact (q0 : ℝ) : IsCompact (shearedModelSquare q0) := by
  rw [shearedModelSquare_eq_image]
  exact modelSquare_isCompact.image (shearCoordinates_contDiff q0).continuous

theorem shearedModelSquare_subset_domain {U : Set Coord} (hSU : modelSquare ⊆ U) (q0 : ℝ) :
    shearedModelSquare q0 ⊆ inverseShearCoordinates q0 ⁻¹' U := fun _ hp => hSU hp

theorem shearedModelDomain_isOpen {U : Set Coord} (hU : IsOpen U) (q0 : ℝ) :
    IsOpen (inverseShearCoordinates q0 ⁻¹' U) :=
  hU.preimage (inverseShearCoordinates_contDiff q0).continuous

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorInitialStateBound
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Pulse SmoothLocal.Flow

theorem actual_initial_sheared_state_bound
    {z : Coord → ℝ} {U : Set Coord} (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hSU : modelSquare ⊆ U) {Z : ℝ} (hZ : 0 ≤ Z)
    (hjet : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z)
    (q0 left right a : ℝ)
    (hcut : ∀ x ∈ Ioo left right, inverseShearCoordinates q0 ![x,a] ∈ modelSquare)
    {x : ℝ} (hx : x ∈ Ioo left right) (hpB : ‖(![x,a] : Coord)‖ ≤ 1) :
    ‖qSolutionJet (linearCauchy a (heightCauchyValue (heightInShearCoordinates z q0) a)
      (heightCauchyVelocity (heightInShearCoordinates z q0) a)) ![x,a]‖ ≤
        initialShearedStateBudget Z q0 := by
  have hz2 : CoordinateBound z modelSquare 2 Z := by
    apply coordinateBound_of_frechet_bounds hz hU hSU
    intro k hk p hp
    exact hjet k (by omega) p hp
  have hzs := heightInShearCoordinates_contDiffOn hz q0
  have hV := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  rw [linearCauchy_height_initial_state hzs hV left right a
    (fun x hx => hSU (hcut x hx)) hx]
  have hb := SmoothLocal.Pulse.CoordinateBound.inverse_shear hz2 hz hU hSU hZ q0
  apply qSolutionJet_norm_bound_of_words (by norm_num) hpB
  intro ds hds
  exact hb ds hds _ (hcut x hx)

end SmoothLocal.Taylor

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

theorem qSolutionJet_positive_fullJet_bound {P : Coord → ℝ} {V : Set Coord}
    (hP : ContDiffOn ℝ ∞ P V) (hV : IsOpen V) {p : Coord} (hp : p ∈ V)
    {n : ℕ} (hn : 1 ≤ n) {B : ℝ}
    (hB : ∀ j ≤ n + 2, ‖iteratedFDeriv ℝ j P p‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (qSolutionJet P) p‖ ≤ max 1 B := by
  apply norm_iteratedFDeriv_pi_le
    ((qSolutionJet_contDiffOn hV hP).contDiffAt (hV.mem_nhds hp)) n
    (zero_le_one.trans (le_max_left _ _))
  intro i
  fin_cases i
  · exact (coordinateProjection_positive_jet_bound 0 p hn).trans (le_max_left _ _)
  · exact (coordinateProjection_positive_jet_bound 1 p hn).trans (le_max_left _ _)
  · exact ((norm_iteratedFDeriv_coordPartial_le hP hV hp 0 n).trans
      (hB (n + 1) (by omega))).trans (le_max_right _ _)
  · exact ((norm_iteratedFDeriv_coordPartial_le hP hV hp 1 n).trans
      (hB (n + 1) (by omega))).trans (le_max_right _ _)
  · exact (((norm_iteratedFDeriv_coordPartial_le (partial_contDiffOn hP hV 1) hV hp 0 n).trans
      (norm_iteratedFDeriv_coordPartial_le hP hV hp 1 (n + 1))).trans
        (hB (n + 1 + 1) (by omega))).trans (le_max_right _ _)
  · exact (((norm_iteratedFDeriv_coordPartial_le (partial_contDiffOn hP hV 0) hV hp 0 n).trans
      (norm_iteratedFDeriv_coordPartial_le hP hV hp 0 (n + 1))).trans
        (hB (n + 1 + 1) (by omega))).trans (le_max_right _ _)

theorem qSolutionJet_mem_qCompactTube {g : MetricField} {P : Coord → ℝ}
    {S : Set Coord} {p : Coord} (hp : p ∈ S) {M c : ℝ}
    (_hM : 0 ≤ M) (hstate : ‖qSolutionJet P p‖ ≤ M)
    (hden : c ≤ |covHessian g P p 0 0|) :
    qSolutionJet P p ∈ qCompactTube g S M c := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change statePoint (qSolutionJet P p) ∈ S
    rw [statePoint_qSolutionJet]
    exact hp
  · constructor <;> intro i
    · exact (abs_le.mp ((norm_le_pi_norm (qSolutionJet P p) i).trans hstate)).1
    · exact (abs_le.mp ((norm_le_pi_norm (qSolutionJet P p) i).trans hstate)).2
  · change c ≤ |stateQDenominator g (qSolutionJet P p)|
    rw [stateQDenominator_qSolutionJet]
    exact hden

end SmoothLocal.Taylor

end

end OAI
end


