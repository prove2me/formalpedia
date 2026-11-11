-- Prove2me | Definitions.Def_Q226II005
-- name    : Q226II005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:38:39.579302+00:00
-- url     : https://prove2.me/theorems/81bf4916-44bf-41b0-87d8-ac5ad8fd1cbd
-- title:
--   Definitions bundle Q226II005 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 355 declarations of OpenAI's Lean: 108 definitions and 247 theorems. The definitions and types are `OAI.SmoothLocal.Geometry.jetXX`, `OAI.SmoothLocal.Geometry.metricFirstJet`, `OAI.SmoothLocal.Geometry.patchAddressModelDomain`, `OAI.SmoothLocal.Geometry.solvedDarbouxQ`, `OAI.SmoothLocal.Geometry.warpedChristoffel`, `OAI.SmoothLocal.HighEquation.HorizontalMetricTwoJetBound`, `OAI.SmoothLocal.HighEquation.QActiveComponents`, `OAI.SmoothLocal.HighEquation.QLowBounds`, `OAI.SmoothLocal.HighEquation.actualQHighRemainder`, `OAI.SmoothLocal.HighEquation.averagedQCoefficient`, `OAI.SmoothLocal.HighEquation.comparisonCoefficient`, `OAI.SmoothLocal.HighEquation.comparisonDifference`, `OAI.SmoothLocal.HighEquation.comparisonIntegrand`, `OAI.SmoothLocal.HighEquation.comparisonParameterDomain`, `OAI.SmoothLocal.HighEquation.comparisonStateMap`, `OAI.SmoothLocal.HighEquation.darbouxQStateDomain`, `OAI.SmoothLocal.HighEquation.heightQCoefficient`, `OAI.SmoothLocal.HighEquation.horizontalJet`, `OAI.SmoothLocal.HighEquation.qChainFactorOrder`, `OAI.SmoothLocal.HighEquation.qChainSliceBudget`, `OAI.SmoothLocal.HighEquation.qCompactTube`, `OAI.SmoothLocal.HighEquation.qCoordinateChainCoefficient`, `OAI.SmoothLocal.HighEquation.qCoordinateChainFactor`, `OAI.SmoothLocal.HighEquation.qCoordinateChainSum`, `OAI.SmoothLocal.HighEquation.qCoordinateChainTerm`, `OAI.SmoothLocal.HighEquation.qDirectLinearization`, `OAI.SmoothLocal.HighEquation.qFirstCoefficient`, `OAI.SmoothLocal.HighEquation.qFirstJetPairRemainder`, `OAI.SmoothLocal.HighEquation.qFixedTimeBaseDomain`, `OAI.SmoothLocal.HighEquation.qFixedTimeDomain`, `OAI.SmoothLocal.HighEquation.qFixedTimeQ`, `OAI.SmoothLocal.HighEquation.qFixedTimeState`, `OAI.SmoothLocal.HighEquation.qHeightJetSegment`, `OAI.SmoothLocal.HighEquation.qHighBTheta`, `OAI.SmoothLocal.HighEquation.qHighBXi`, `OAI.SmoothLocal.HighEquation.qRemainderSliceBudget`, `OAI.SmoothLocal.HighEquation.qSecondJetCorrection`, `OAI.SmoothLocal.HighEquation.qSolutionJet`, `OAI.SmoothLocal.HighEquation.qSolutionJetCurve`, `OAI.SmoothLocal.HighEquation.qSpatialCLM` and 68 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Assembly_SupportedPerturbations`, `IsometricImmersion_Calculus_HorizontalJetCalculus`, `IsometricImmersion_Calculus_MovingFirstJetBase`, `IsometricImmersion_Calculus_MovingIntervalCalculus`, `IsometricImmersion_Calculus_ShearHeightJets`, `IsometricImmersion_Calculus_ShearMetricJets`, `IsometricImmersion_Calculus_StateJetSegment`, `IsometricImmersion_Caps_ActualLowerCutImage`, `IsometricImmersion_Caps_PulseCapSeparation`, `IsometricImmersion_Caps_QPointwiseCauchyJets`, `IsometricImmersion_Comparison_ActualComparisonEquation`, `IsometricImmersion_Comparison_ComparisonCoefficientSmooth`, `IsometricImmersion_Comparison_CurvatureComparisonControl`, `IsometricImmersion_Comparison_FiniteApproximationJets`, `IsometricImmersion_Comparison_ShearFirstJetComparison`, `IsometricImmersion_Coordinates_ActualPatchQRectangle`, `IsometricImmersion_Coordinates_BoundedClassSlabSmallness`, `IsometricImmersion_Coordinates_BoundedPatchSlabGeometry`, `IsometricImmersion_Coordinates_CoordinateSwap`, `IsometricImmersion_Coordinates_PatchAddressModel`, `IsometricImmersion_Curvature_CurvatureLowerTube`, `IsometricImmersion_Curvature_CurvatureParameter`, `IsometricImmersion_Curvature_PrescribedCurvature`, `IsometricImmersion_Darboux_CurvaturePrincipalPart`, `IsometricImmersion_Darboux_QActualSegmentTransfer`, `IsometricImmersion_Darboux_QCoefficientTube`, `IsometricImmersion_Darboux_QContainingRectangle`, `IsometricImmersion_Darboux_QEnergyApplication`, `IsometricImmersion_Darboux_QFirstJetEnergy`, `IsometricImmersion_Darboux_QFirstJetFunctions`, `IsometricImmersion_Darboux_QFirstSpatialBounds`, `IsometricImmersion_Darboux_QHighEquation`, `IsometricImmersion_Darboux_QLowActualBounds`, `IsometricImmersion_Darboux_QPrincipal`, `IsometricImmersion_Darboux_QResidualActive`, `IsometricImmersion_Darboux_QResidualFactors`, `IsometricImmersion_Darboux_QResidualL2`, `IsometricImmersion_Darboux_QSameStripMargins`, `IsometricImmersion_Darboux_QSegmentAveraging`, `IsometricImmersion_Darboux_QSegmentDomain`, `IsometricImmersion_Darboux_QSpatialJets`, `IsometricImmersion_Darboux_QSpatialRestriction`, `IsometricImmersion_Darboux_QSpatialSlabData`, `IsometricImmersion_Darboux_SixVariableQ`, `IsometricImmersion_Darboux_SwappedDarboux`, `IsometricImmersion_Energy_HyperbolicEnergyDensity`, `IsometricImmersion_Energy_LocalQResidualL2`, `IsometricImmersion_Energy_MovingHyperbolicEnergy`, `IsometricImmersion_Energy_MovingIntervalSobolev`, `IsometricImmersion_Energy_MovingIntervalSourceL2`, `IsometricImmersion_Energy_MovingSlabEnergy`, `IsometricImmersion_Energy_SqrtEnergyGronwall`, `IsometricImmersion_Immersions_ActualShearHeight`, `IsometricImmersion_Metrics_LocalMetricQActive`, `IsometricImmersion_Metrics_MetricHorizontalRequests`, `IsometricImmersion_Metrics_MetricPatchOpen`, `IsometricImmersion_Metrics_MetricQSpatialBundle`, `IsometricImmersion_Metrics_StateCoefficientTube`, `IsometricImmersion_Metrics_WarpedMetric`, `IsometricImmersion_Pulses_PulseCurvaturePrincipal`, `IsometricImmersion_Pulses_PulseDerivativeBounds`, `IsometricImmersion_Pulses_PulseEdgeReferenceDistance`, `IsometricImmersion_Pulses_PulseFlowDistance`, `IsometricImmersion_Pulses_PulseMomentGeometry`, `IsometricImmersion_Pulses_PulseNeighborhood`, `IsometricImmersion_Pulses_PulseOperatorMoment`, `IsometricImmersion_Pulses_PulseProfiles`, `IsometricImmersion_Pulses_PulseSpatialParts`, `IsometricImmersion_Pulses_PulseTemporalMoment`, `IsometricImmersion_Pulses_PulseTemporalParts`, `IsometricImmersion_Pulses_PulseTestEnergy`, `IsometricImmersion_Pulses_ShearedPulseRegions`, `IsometricImmersion_Taylor_TaylorCauchyData`, `IsometricImmersion_Taylor_TaylorInitialStateBound`, `IsometricImmersion_Taylor_TaylorResidual`, `IsometricImmersion_Volterra_VolterraDifferentiation`, `IsometricImmersion_Volterra_VolterraInverse`, `IsometricImmersion_Volterra_VolterraOperator`, `IsometricImmersion_Volterra_VolterraPositive`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II000`, `Q226II001` and `Q226II002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q226II008`, `Q226II009` and `Q226II010`.
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
import Definitions.Def_Q226II000
import Definitions.Def_Q226II001
import Definitions.Def_Q226II002

section
-- module Solutions.Q226_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_WarpedMetric
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

theorem inverseMetric_warpedMetric (f : Coord → ℝ) {p : Coord} (hne : f p ≠ 0) :
    inverseMetric (warpedMetric f) p = Matrix.diagonal ![1, ((f p) ^ 2)⁻¹] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [warpedMetric, Matrix.mul_apply, Fin.sum_univ_two, hne]

theorem coordPartial_mul {f h : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q * h q) p =
      coordPartial i f p * h p + f p * coordPartial i h p := by
  simp [coordPartial, fderiv_fun_mul hf hh, add_comm, mul_comm]

theorem coordPartial_neg (f : Coord → ℝ) (i : Fin 2) (p : Coord) :
    coordPartial i (fun q => -f q) p = -coordPartial i f p := by
  simp [coordPartial, fderiv_fun_neg]

theorem coordPartial_sq {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (i : Fin 2) :
    coordPartial i (fun q => (f q) ^ 2) p = 2 * f p * coordPartial i f p := by
  simp only [pow_two]
  rw [coordPartial_mul hf hf]
  ring

theorem coordPartial_warpedMetric {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (i j k : Fin 2) :
    coordPartial i (fun q => warpedMetric f q j k) p =
      if j = 1 ∧ k = 1 then 2 * f p * coordPartial i f p else 0 := by
  fin_cases j <;> fin_cases k <;> simp [coordPartial_sq hf]

def warpedChristoffel (f : Coord → ℝ) (k i j : Fin 2) (p : Coord) : ℝ :=
  if k = 0 then
    if i = 1 ∧ j = 1 then -(f p * coordPartial 0 f p) else 0
  else if i = 0 ∧ j = 0 then 0
  else if i = 1 ∧ j = 1 then coordPartial 1 f p / f p
  else coordPartial 0 f p / f p

theorem christoffel_warpedMetric {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (hne : f p ≠ 0) (k i j : Fin 2) :
    christoffel (warpedMetric f) k i j p = warpedChristoffel f k i j p := by
  simp only [christoffel, Fin.sum_univ_two, inverseMetric_warpedMetric f hne,
    coordPartial_warpedMetric hf]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [warpedChristoffel] <;> field_simp [hne]

theorem riemann_warpedMetric_0101 {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (hne : ∀ q ∈ U, f q ≠ 0) {p : Coord} (hp : p ∈ U) :
    riemann (warpedMetric f) 0 1 0 1 p =
      -(f p * coordPartial 0 (coordPartial 0 f) p) := by
  have hd (q : Coord) (hq : q ∈ U) : DifferentiableAt ℝ f q :=
    ((hf q hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdX : DifferentiableAt ℝ (coordPartial 0 f) p :=
    (((partial_contDiffOn hf hU 0) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h011 : christoffel (warpedMetric f) 0 1 1 =ᶠ[𝓝 p]
      (fun q => -(f q * coordPartial 0 f q)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    simpa [warpedChristoffel] using christoffel_warpedMetric (hd q hq) (hne q hq) 0 1 1
  have h001 : christoffel (warpedMetric f) 0 0 1 =ᶠ[𝓝 p]
      (fun _ : Coord => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    simpa [warpedChristoffel] using christoffel_warpedMetric (hd q hq) (hne q hq) 0 0 1
  have d011 : coordPartial 0 (christoffel (warpedMetric f) 0 1 1) p =
      -(coordPartial 0 f p * coordPartial 0 f p +
        f p * coordPartial 0 (coordPartial 0 f) p) := by
    change fderiv ℝ (christoffel (warpedMetric f) 0 1 1) p (Pi.single 0 1) = _
    rw [h011.fderiv_eq]
    change coordPartial 0 (fun q => -(f q * coordPartial 0 f q)) p = _
    rw [coordPartial_neg, coordPartial_mul (hd p hp) hdX]
  have d001 : coordPartial 1 (christoffel (warpedMetric f) 0 0 1) p = 0 := by
    change fderiv ℝ (christoffel (warpedMetric f) 0 0 1) p (Pi.single 1 1) = _
    rw [h001.fderiv_eq]
    simp
  simp only [riemann, d011, d001, Fin.sum_univ_two,
    christoffel_warpedMetric (hd p hp) (hne p hp)]
  simp [warpedChristoffel]
  field_simp [hne p hp]
  ring

theorem gaussianCurvature_warpedMetric {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (hne : ∀ q ∈ U, f q ≠ 0) {p : Coord} (hp : p ∈ U) :
    gaussianCurvature (warpedMetric f) p =
      -coordPartial 0 (coordPartial 0 f) p / f p := by
  simp only [gaussianCurvature, Fin.sum_univ_two, warpedMetric_00,
    warpedMetric_01, warpedMetric_det, one_mul, zero_mul, add_zero]
  rw [riemann_warpedMetric_0101 hf hU hne hp]
  field_simp [hne p hp]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Volterra_VolterraOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology Interval

namespace SmoothLocal.ODE

theorem primitiveCLM_norm_le (r : ℝ) (hr : 0 < r) :
    ‖primitiveCLM r hr‖ ≤ r :=
  LinearMap.mkContinuous_norm_le (primitiveLinearMap r hr) hr.le (primitiveMap_norm_le r hr)

def volterraCLM (r : ℝ) (hr : 0 < r) :
    IntervalFunctions r →L[ℝ] IntervalFunctions r :=
  (primitiveCLM r hr).comp (primitiveCLM r hr)

theorem volterraCLM_norm_le (r : ℝ) (hr : 0 < r) : ‖volterraCLM r hr‖ ≤ r ^ 2 := by
  calc
    ‖volterraCLM r hr‖ ≤ ‖primitiveCLM r hr‖ * ‖primitiveCLM r hr‖ :=
      (primitiveCLM r hr).opNorm_comp_le (primitiveCLM r hr)
    _ ≤ r * r := mul_le_mul (primitiveCLM_norm_le r hr) (primitiveCLM_norm_le r hr)
      (ContinuousLinearMap.opNorm_nonneg _) hr.le
    _ = r ^ 2 := (pow_two r).symm

theorem volterraCLM_norm_le_one (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ‖volterraCLM r hr‖ ≤ 1 := by
  have hh := volterraCLM_norm_le r hr
  have hrr : r * r ≤ 1 * 1 := mul_le_mul hr1 hr1 hr.le zero_le_one
  nlinarith

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Volterra_VolterraInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology

namespace SmoothLocal.ODE

def curvatureVolterraCLM (r : ℝ) (hr : 0 < r) (k : IntervalFunctions r) :
    IntervalFunctions r →L[ℝ] IntervalFunctions r :=
  (volterraCLM r hr).comp (ContinuousLinearMap.mul ℝ (IntervalFunctions r) k)

theorem curvatureVolterraCLM_norm_le (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) : ‖curvatureVolterraCLM r hr k‖ ≤ ‖k‖ := by
  calc
    ‖curvatureVolterraCLM r hr k‖ ≤
        ‖volterraCLM r hr‖ * ‖ContinuousLinearMap.mul ℝ (IntervalFunctions r) k‖ :=
      (volterraCLM r hr).opNorm_comp_le _
    _ ≤ 1 * ‖k‖ := mul_le_mul (volterraCLM_norm_le_one r hr hr1)
      (ContinuousLinearMap.opNorm_mul_apply_le ℝ (IntervalFunctions r) k)
      (norm_nonneg _) zero_le_one
    _ = ‖k‖ := one_mul _

theorem curvatureVolterraCLM_contDiff (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ ∞ (curvatureVolterraCLM r hr) := by
  have hmul : ContDiff ℝ ∞ (ContinuousLinearMap.mul ℝ (IntervalFunctions r)) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (E := IntervalFunctions r) (F := IntervalFunctions r →L[ℝ] IntervalFunctions r)
      (ContinuousLinearMap.mul ℝ (IntervalFunctions r))
  exact (contDiff_const : ContDiff ℝ ∞
    (fun _ : IntervalFunctions r => volterraCLM r hr)).clm_comp hmul

theorem one_add_curvatureVolterra_isUnit (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000) :
    IsUnit (1 + curvatureVolterraCLM r hr k) := by
  have hT : ‖curvatureVolterraCLM r hr k‖ < 1 :=
    lt_of_le_of_lt ((curvatureVolterraCLM_norm_le r hr hr1 k).trans hk) (by norm_num)
  have hneg : ‖-curvatureVolterraCLM r hr k‖ < 1 := by
    rw [ContinuousLinearMap.opNorm_neg]
    exact hT
  simpa only [sub_neg_eq_add] using
    (isUnit_one_sub_of_norm_lt_one
      (R := IntervalFunctions r →L[ℝ] IntervalFunctions r)
      (x := -curvatureVolterraCLM r hr k) hneg)

def volterraSolution (r : ℝ) (hr : 0 < r) (k : IntervalFunctions r) : IntervalFunctions r :=
  Ring.inverse (1 + curvatureVolterraCLM r hr k) 1

theorem volterraSolution_equation (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000) :
    volterraSolution r hr k + volterraCLM r hr (k * volterraSolution r hr k) = 1 := by
  have hunit := one_add_curvatureVolterra_isUnit r hr hr1 k hk
  have he := congrArg (fun L : IntervalFunctions r →L[ℝ] IntervalFunctions r => L 1)
    (Ring.mul_inverse_cancel (1 + curvatureVolterraCLM r hr k) hunit)
  change volterraSolution r hr k +
    volterraCLM r hr (k * volterraSolution r hr k) = 1 at he
  exact he

theorem volterraSolution_contDiffAt (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000) :
    ContDiffAt ℝ ∞ (volterraSolution r hr) k := by
  obtain ⟨u, hu⟩ := one_add_curvatureVolterra_isUnit r hr hr1 k hk
  have hinv : ContDiffAt ℝ ∞
      (Ring.inverse : (IntervalFunctions r →L[ℝ] IntervalFunctions r) →
        (IntervalFunctions r →L[ℝ] IntervalFunctions r))
      (1 + curvatureVolterraCLM r hr k) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ
      (R := IntervalFunctions r →L[ℝ] IntervalFunctions r) (n := ∞) u
  have harg : ContDiffAt ℝ ∞
      (fun q : IntervalFunctions r => 1 + curvatureVolterraCLM r hr q) k :=
    contDiffAt_const.add (curvatureVolterraCLM_contDiff r hr).contDiffAt
  exact (hinv.comp k harg).clm_apply contDiffAt_const

theorem volterraSolution_family_contDiffOn
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    {s : Set P} {K : P → IntervalFunctions r}
    (hK : ContDiffOn ℝ ∞ K s)
    (hbound : ∀ y ∈ s, ‖K y‖ ≤ (1 : ℝ) / 1000) :
    ContDiffOn ℝ ∞ (fun y => volterraSolution r hr (K y)) s := by
  intro y hy
  exact (volterraSolution_contDiffAt r hr hr1 (K y) (hbound y hy)).comp_contDiffWithinAt
    y (hK y hy)

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_CurvatureParameter
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

theorem coordinatePoint_mem_square {x y : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    coordinatePoint x y ∈ square := by
  intro i
  fin_cases i
  · simpa [coordinatePoint] using hx
  · simpa [coordinatePoint] using hy

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Volterra_VolterraDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

theorem intervalExtension_mul (r : ℝ) (hr : 0 < r)
    (h k : IntervalFunctions r) (x : ℝ) :
    intervalExtension r hr (h * k) x =
      intervalExtension r hr h x * intervalExtension r hr k x := rfl

def volterraScalar (r : ℝ) (hr : 0 < r) (k : IntervalFunctions r) (x : ℝ) : ℝ :=
  intervalExtension r hr (volterraSolution r hr k) x

def volterraVelocity (r : ℝ) (hr : 0 < r) (k : IntervalFunctions r) (x : ℝ) : ℝ :=
  -primitiveFunction r hr (k * volterraSolution r hr k) x

theorem volterraScalar_hasDerivAt (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000)
    {x : ℝ} (hx : x ∈ Ioo (-r) r) :
    HasDerivAt (volterraScalar r hr k) (volterraVelocity r hr k x) x := by
  let g := k * volterraSolution r hr k
  have hd := (primitiveFunction_hasDerivAt r hr (primitiveCLM r hr g) x).const_sub 1
  rw [intervalExtension_apply_of_mem r hr _ ⟨hx.1.le, hx.2.le⟩] at hd
  change HasDerivAt (fun t => 1 - primitiveFunction r hr (primitiveCLM r hr g) t)
    (volterraVelocity r hr k x) x at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  have htc : t ∈ Icc (-r) r := ⟨ht.1.le, ht.2.le⟩
  have he := congrArg (fun h : IntervalFunctions r => h ⟨t, htc⟩)
    (volterraSolution_equation r hr hr1 k hk)
  change volterraSolution r hr k ⟨t, htc⟩ +
    primitiveFunction r hr (primitiveCLM r hr g) t = 1 at he
  unfold volterraScalar
  rw [intervalExtension_apply_of_mem r hr _ htc]
  linarith

theorem volterraVelocity_hasDerivAt (r : ℝ) (hr : 0 < r)
    (k : IntervalFunctions r) (x : ℝ) :
    HasDerivAt (volterraVelocity r hr k)
      (-intervalExtension r hr k x * volterraScalar r hr k x) x := by
  change HasDerivAt (fun t => -primitiveFunction r hr (k * volterraSolution r hr k) t)
    (-intervalExtension r hr k x * intervalExtension r hr (volterraSolution r hr k) x) x
  simpa only [Pi.neg_def, intervalExtension_mul, neg_mul] using
    (primitiveFunction_hasDerivAt r hr (k * volterraSolution r hr k) x).neg

theorem volterraScalar_initial (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000) :
    volterraScalar r hr k 0 = 1 := by
  have hz : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr.le⟩
  have he := congrArg (fun h : IntervalFunctions r => h ⟨0, hz⟩)
    (volterraSolution_equation r hr hr1 k hk)
  change volterraSolution r hr k ⟨0, hz⟩ +
    primitiveFunction r hr (primitiveCLM r hr (k * volterraSolution r hr k)) 0 = 1 at he
  simpa [volterraScalar, intervalExtension_apply_of_mem r hr _ hz, primitiveFunction] using he

theorem volterraVelocity_initial (r : ℝ) (hr : 0 < r) (k : IntervalFunctions r) :
    volterraVelocity r hr k 0 = 0 := by
  simp [volterraVelocity, primitiveFunction]

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Volterra_VolterraPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Topology

namespace SmoothLocal.ODE

theorem volterraSolution_norm_le (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000) :
    ‖volterraSolution r hr k‖ ≤ (1000 : ℝ) / 999 := by
  let : Nonempty (Icc (-r) r) := ⟨⟨0, ⟨by linarith, hr.le⟩⟩⟩
  let f := volterraSolution r hr k
  let T := curvatureVolterraCLM r hr k
  have hT : ‖T‖ ≤ (1 : ℝ) / 1000 := (curvatureVolterraCLM_norm_le r hr hr1 k).trans hk
  have he : f + T f = 1 := volterraSolution_equation r hr hr1 k hk
  have he' : f = 1 - T f := eq_sub_of_add_eq he
  have hn : ‖f‖ ≤ 1 + (1 : ℝ) / 1000 * ‖f‖ := by
    calc
      ‖f‖ = ‖1 - T f‖ := congrArg norm he'
      _ ≤ ‖(1 : IntervalFunctions r)‖ + ‖T f‖ := norm_sub_le _ _
      _ ≤ 1 + (1 : ℝ) / 1000 * ‖f‖ := by
        rw [norm_one]
        exact add_le_add le_rfl ((T.le_opNorm f).trans
          (mul_le_mul_of_nonneg_right hT (norm_nonneg f)))
  change ‖f‖ ≤ (1000 : ℝ) / 999
  linarith

theorem volterraSolution_sub_one_norm_le (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000) :
    ‖volterraSolution r hr k - 1‖ ≤ (1 : ℝ) / 999 := by
  let f := volterraSolution r hr k
  let T := curvatureVolterraCLM r hr k
  have he : f + T f = 1 := volterraSolution_equation r hr hr1 k hk
  have hsub : f - 1 = -(T f) := by
    calc
      f - 1 = (1 - T f) - 1 := congrArg (fun v => v - 1) (eq_sub_of_add_eq he)
      _ = -(T f) := by abel
  have hT : ‖T‖ ≤ (1 : ℝ) / 1000 := (curvatureVolterraCLM_norm_le r hr hr1 k).trans hk
  change ‖f - 1‖ ≤ (1 : ℝ) / 999
  rw [hsub, norm_neg]
  calc
    ‖T f‖ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
    _ ≤ ((1 : ℝ) / 1000) * (1000 / 999) := mul_le_mul hT
      (volterraSolution_norm_le r hr hr1 k hk) (norm_nonneg f) (by norm_num)
    _ = (1 : ℝ) / 999 := by norm_num

theorem volterraScalar_bounds (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000) (x : ℝ) :
    (998 : ℝ) / 999 ≤ volterraScalar r hr k x ∧
      volterraScalar r hr k x ≤ (1000 : ℝ) / 999 ∧ 0 < volterraScalar r hr k x := by
  have hn := (intervalExtension_norm_le r hr (volterraSolution r hr k - 1) x).trans
    (volterraSolution_sub_one_norm_le r hr hr1 k hk)
  change ‖volterraScalar r hr k x - 1‖ ≤ (1 : ℝ) / 999 at hn
  rw [Real.norm_eq_abs] at hn
  have hb := abs_le.mp hn
  constructor
  · linarith [hb.1]
  constructor
  · linarith [hb.2]
  · linarith [hb.1]

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_PrescribedCurvature
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

theorem coordinatePoint_eta (p : Coord) : coordinatePoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> simp [coordinatePoint]

theorem coordinatePoint_hasDerivAt_x (x y : ℝ) :
    HasDerivAt (fun t => coordinatePoint t y) (Pi.single 0 (1 : ℝ) : Coord) x := by
  simpa [coordinatePoint] using
    ((hasDerivAt_id x).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add_const
      (y • (Pi.single 1 (1 : ℝ) : Coord))

theorem coordinateSlice_hasDerivAt_x {f : Coord → ℝ}
    (hf : ContDiffOn ℝ ∞ f square) {p : Coord} (hp : p ∈ square) :
    HasDerivAt (fun t => f (coordinatePoint t (p 1))) (coordPartial 0 f p) (p 0) := by
  have hd : DifferentiableAt ℝ f (coordinatePoint (p 0) (p 1)) := by
    rw [coordinatePoint_eta]
    exact (hf.contDiffAt (coordinate_square_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hh := hd.hasFDerivAt.comp_hasDerivAt (p 0)
    (coordinatePoint_hasDerivAt_x (p 0) (p 1))
  simpa only [coordinatePoint_eta, Function.comp_def, coordPartial] using hh

end SmoothLocal.ODE

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

def modelSquare : Set Coord := Icc (fun _ => (-3 : ℝ)) (fun _ => (3 : ℝ))

theorem modelSquare_isCompact : IsCompact modelSquare := isCompact_Icc

theorem patchBox_subset_modelSquare : patchBox ⊆ modelSquare := by
  intro p hp
  constructor <;> intro i <;> linarith [hp.1 i, hp.2 i]

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_HyperbolicEnergyDensity
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

def hyperbolicOperator (P S v : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 1 (coordPartial 1 v) p -
    P p * coordPartial 0 (coordPartial 1 v) p -
    S p * coordPartial 0 (coordPartial 0 v) p

def energyDensity (S v : Coord → ℝ) (p : Coord) : ℝ :=
  ((coordPartial 1 v p) ^ 2 + S p * (coordPartial 0 v p) ^ 2) / 2

def energyFlux (P S v : Coord → ℝ) (p : Coord) : ℝ :=
  P p * (coordPartial 1 v p) ^ 2 / 2 +
    S p * coordPartial 0 v p * coordPartial 1 v p

def energyCoefficientError (P S bTheta bXi v : Coord → ℝ) (p : Coord) : ℝ :=
  (bTheta p - coordPartial 0 P p / 2) * (coordPartial 1 v p) ^ 2 +
    (bXi p - coordPartial 0 S p) * coordPartial 0 v p * coordPartial 1 v p +
    coordPartial 1 S p / 2 * (coordPartial 0 v p) ^ 2

variable {P S bTheta bXi v R : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem energyDensity_partial_theta
    (hS : DifferentiableAt ℝ S p)
    (hvt : DifferentiableAt ℝ (coordPartial 1 v) p)
    (hvx : DifferentiableAt ℝ (coordPartial 0 v) p) :
    coordPartial 1 (energyDensity S v) p =
      coordPartial 1 v p * coordPartial 1 (coordPartial 1 v) p +
      S p * coordPartial 0 v p * coordPartial 1 (coordPartial 0 v) p +
      coordPartial 1 S p / 2 * (coordPartial 0 v p) ^ 2 := by
  have hd := ((hvt.hasFDerivAt.fun_mul hvt.hasFDerivAt).add
    (hS.hasFDerivAt.fun_mul (hvx.hasFDerivAt.fun_mul hvx.hasFDerivAt))).mul_const
      (1 / 2 : ℝ)
  simp only [Pi.add_def, coordPartial, one_div] at hd
  unfold energyDensity
  simp only [div_eq_mul_inv, pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem energyFlux_partial_xi
    (hP : DifferentiableAt ℝ P p) (hS : DifferentiableAt ℝ S p)
    (hvt : DifferentiableAt ℝ (coordPartial 1 v) p)
    (hvx : DifferentiableAt ℝ (coordPartial 0 v) p) :
    coordPartial 0 (energyFlux P S v) p =
      coordPartial 0 P p / 2 * (coordPartial 1 v p) ^ 2 +
      P p * coordPartial 1 v p * coordPartial 0 (coordPartial 1 v) p +
      coordPartial 0 S p * coordPartial 0 v p * coordPartial 1 v p +
      S p * coordPartial 0 (coordPartial 0 v) p * coordPartial 1 v p +
      S p * coordPartial 0 v p * coordPartial 0 (coordPartial 1 v) p := by
  have hd := ((hP.hasFDerivAt.fun_mul
    (hvt.hasFDerivAt.fun_mul hvt.hasFDerivAt)).mul_const (1 / 2 : ℝ)).add
      ((hS.hasFDerivAt.fun_mul hvx.hasFDerivAt).fun_mul hvt.hasFDerivAt)
  simp only [Pi.add_def, coordPartial, one_div] at hd
  unfold energyFlux
  simp only [div_eq_mul_inv, pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem energy_fields_contDiffOn
    (hU : IsOpen U) (hP : ContDiffOn ℝ ∞ P U) (hS : ContDiffOn ℝ ∞ S U)
    (hbt : ContDiffOn ℝ ∞ bTheta U) (hbx : ContDiffOn ℝ ∞ bXi U)
    (hv : ContDiffOn ℝ ∞ v U) :
    ContDiffOn ℝ ∞ (energyDensity S v) U ∧
    ContDiffOn ℝ ∞ (energyFlux P S v) U ∧
    ContDiffOn ℝ ∞ (energyCoefficientError P S bTheta bXi v) U := by
  have ht := partial_contDiffOn hv hU 1
  have hx := partial_contDiffOn hv hU 0
  have hPx := partial_contDiffOn hP hU 0
  have hSx := partial_contDiffOn hS hU 0
  have hSt := partial_contDiffOn hS hU 1
  exact ⟨((ht.pow 2).add (hS.mul (hx.pow 2))).div_const 2,
    ((hP.mul (ht.pow 2)).div_const 2).add ((hS.mul hx).mul ht),
    (((hbt.sub (hPx.div_const 2)).mul (ht.pow 2)).add
      (((hbx.sub hSx).mul hx).mul ht)).add ((hSt.div_const 2).mul (hx.pow 2))⟩

theorem energyDensity_nonneg (hS : 0 ≤ S p) : 0 ≤ energyDensity S v p := by
  unfold energyDensity
  positivity

theorem energyFlux_abs_le (hS : 0 ≤ S p) :
    |energyFlux P S v p| ≤ (|P p| + Real.sqrt (S p)) * energyDensity S v p :=
  scalar_flux_bound (P p) (S p) (coordPartial 1 v p) (coordPartial 0 v p) hS

theorem inward_boundary_nonpositive {left right : Coord} {c : ℝ}
    (hSl : 0 ≤ S left) (hSr : 0 ≤ S right)
    (hcl : |P left| + Real.sqrt (S left) ≤ c)
    (hcr : |P right| + Real.sqrt (S right) ≤ c) :
    energyFlux P S v right - energyFlux P S v left -
      c * (energyDensity S v right + energyDensity S v left) ≤ 0 := by
  have hl := (energyFlux_abs_le (P := P) (v := v) hSl).trans
    (mul_le_mul_of_nonneg_right hcl (energyDensity_nonneg (v := v) hSl))
  have hr := (energyFlux_abs_le (P := P) (v := v) hSr).trans
    (mul_le_mul_of_nonneg_right hcr (energyDensity_nonneg (v := v) hSr))
  have hll := (abs_le.mp hl).1
  have hrr := (abs_le.mp hr).2
  linarith

theorem energyCoefficientError_abs_le
    {s0 M : ℝ} (hs0 : 0 < s0) (hS : s0 ≤ S p) (hM : 0 ≤ M)
    (hbt : |bTheta p| ≤ M) (hbx : |bXi p| ≤ M)
    (hPx : |coordPartial 0 P p| ≤ M) (hSx : |coordPartial 0 S p| ≤ M)
    (hSt : |coordPartial 1 S p| ≤ M) :
    |energyCoefficientError P S bTheta bXi v p| ≤
      (8 * M * (1 + 1 / s0)) * energyDensity S v p :=
  scalar_coefficient_error_bound hs0 hS hM hbt hbx hPx hSx hSt

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_MovingIntervalCalculus
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

def movingIntervalIntegral (left right : ℝ → ℝ) (f : Coord → ℝ) (theta : ℝ) : ℝ :=
  ∫ xi in left theta..right theta, f (coordinatePoint xi theta)

theorem movingPoint_hasDerivAt {x : ℝ → ℝ} {dx theta : ℝ}
    (hx : HasDerivAt x dx theta) :
    HasDerivAt (fun t => coordinatePoint (x t) t)
      (dx • Pi.single 0 (1 : ℝ) + Pi.single 1 (1 : ℝ) : Coord) theta := by
  simpa only [coordinatePoint, one_smul, id_eq, Pi.add_def] using
    (hx.smul_const (Pi.single 0 (1 : ℝ) : Coord)).add
      ((hasDerivAt_id theta).smul_const (Pi.single 1 (1 : ℝ) : Coord))

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MovingHyperbolicEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

def movingEnergy (xl xr theta0 speed : ℝ) (S v : Coord → ℝ) : ℝ → ℝ :=
  movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
    (energyDensity S v)

def movingEnergyRate (xl xr theta0 speed : ℝ) (P S bTheta bXi v R : Coord → ℝ)
    (theta : ℝ) : ℝ :=
  energyFlux P S v (coordinatePoint (inwardRight xr theta0 speed theta) theta) -
    energyFlux P S v (coordinatePoint (inwardLeft xl theta0 speed theta) theta) -
    speed * (energyDensity S v (coordinatePoint (inwardRight xr theta0 speed theta) theta) +
      energyDensity S v (coordinatePoint (inwardLeft xl theta0 speed theta) theta)) +
    movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
      (fun p => energyCoefficientError P S bTheta bXi v p + R p * coordPartial 1 v p) theta

def movingSourceNorm (xl xr theta0 speed : ℝ) (R : Coord → ℝ) (theta : ℝ) : ℝ :=
  Real.sqrt (movingIntervalIntegral (inwardLeft xl theta0 speed)
    (inwardRight xr theta0 speed) (fun p => R p ^ 2) theta)

variable {P S bTheta bXi v R : Coord → ℝ} {radius lo hi xl xr theta0 speed theta : ℝ}

theorem movingEnergy_nonneg
    (hlr : inwardLeft xl theta0 speed theta ≤ inwardRight xr theta0 speed theta)
    (hS : ∀ x ∈ Icc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta),
      0 ≤ S (coordinatePoint x theta)) :
    0 ≤ movingEnergy xl xr theta0 speed S v theta := by
  exact intervalIntegral.integral_nonneg hlr (fun x hx => energyDensity_nonneg (hS x hx))

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_SqrtEnergyGronwall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace SmoothLocal.Hyperbolic

theorem regularizedWeightedRate_le
    {E Ed force : ℝ → ℝ} {C a eta t : ℝ} (hE : 0 ≤ E t)
    (hforce : 0 ≤ force t) (hC : 0 ≤ C) (heta : 0 < eta) (hat : a ≤ t)
    (hEd : Ed t ≤ C * E t + Real.sqrt (2 * E t) * force t) :
    regularizedWeightedRate E Ed C a eta t ≤ force t := by
  have hy := regularized_sqrt_rate_le hE hforce hC heta hEd
  have hfactor : Real.exp (-C * (t - a)) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    nlinarith
  have hfpos := (Real.exp_pos (-C * (t - a))).le
  have hmul := mul_le_mul_of_nonneg_left (show
    Ed t / (2 * Real.sqrt (E t + eta)) - C * Real.sqrt (E t + eta) ≤ force t by linarith) hfpos
  exact hmul.trans (by nlinarith [mul_le_mul_of_nonneg_right hfactor hforce])

theorem regularized_sqrt_energy_gronwall
    {E Ed force : ℝ → ℝ} {C a b eta : ℝ} (hab : a ≤ b)
    (hEcont : ContinuousOn E (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt E (Ed t) t)
    (hE : ∀ t ∈ Icc a b, 0 ≤ E t)
    (hforce : ContinuousOn force (Icc a b))
    (hforcepos : ∀ t ∈ Icc a b, 0 ≤ force t)
    (hC : 0 ≤ C) (heta : 0 < eta)
    (hineq : ∀ t ∈ Ioo a b, Ed t ≤ C * E t + Real.sqrt (2 * E t) * force t) :
    Real.sqrt (E b + eta) ≤ Real.exp (C * (b - a)) *
      (Real.sqrt (E a + eta) + ∫ t in a..b, force t) := by
  have hwcont : ContinuousOn (regularizedWeightedEnergy E C a eta) (Icc a b) := by
    exact (show Continuous (fun t : ℝ => Real.exp (-C * (t - a))) by fun_prop).continuousOn.mul
      ((hEcont.add continuousOn_const).sqrt)
  have hwderiv (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivWithinAt (regularizedWeightedEnergy E C a eta)
        (regularizedWeightedRate E Ed C a eta t) (Ioi t) t :=
    (regularizedWeightedEnergy_hasDerivAt (hderiv t ht)
      (hE t ⟨ht.1.le, ht.2.le⟩) heta).hasDerivWithinAt
  have hint := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hwcont hwderiv
    (hforce.integrableOn_compact isCompact_Icc) (fun t ht =>
      regularizedWeightedRate_le (hE t ⟨ht.1.le, ht.2.le⟩)
        (hforcepos t ⟨ht.1.le, ht.2.le⟩) hC heta ht.1.le (hineq t ht))
  have hw : Real.exp (-C * (b - a)) * Real.sqrt (E b + eta) ≤
      Real.sqrt (E a + eta) + ∫ t in a..b, force t := by
    simpa only [regularizedWeightedEnergy, sub_self, mul_zero, Real.exp_zero, one_mul,
      sub_le_iff_le_add, add_comm] using hint
  have hmul := mul_le_mul_of_nonneg_left hw (Real.exp_pos (C * (b - a))).le
  have hexp : Real.exp (C * (b - a)) * Real.exp (-C * (b - a)) = 1 := by
    rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
  simpa only [← mul_assoc, hexp, one_mul] using hmul

theorem sqrt_energy_gronwall
    {E Ed force : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (hEcont : ContinuousOn E (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt E (Ed t) t)
    (hE : ∀ t ∈ Icc a b, 0 ≤ E t)
    (hforce : ContinuousOn force (Icc a b))
    (hforcepos : ∀ t ∈ Icc a b, 0 ≤ force t)
    (hC : 0 ≤ C)
    (hineq : ∀ t ∈ Ioo a b, Ed t ≤ C * E t + Real.sqrt (2 * E t) * force t) :
    Real.sqrt (E b) ≤ Real.exp (C * (b - a)) *
      (Real.sqrt (E a) + ∫ t in a..b, force t) := by
  have ht0 : Tendsto (fun eta : ℝ => eta) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuousWithinAt_id.tendsto
  have hleft : Tendsto (fun eta : ℝ => Real.sqrt (E b + eta))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt (E b))) := by
    simpa only [add_zero] using (tendsto_const_nhds.add ht0).sqrt
  have hright : Tendsto (fun eta : ℝ => Real.exp (C * (b - a)) *
      (Real.sqrt (E a + eta) + ∫ t in a..b, force t)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.exp (C * (b - a)) * (Real.sqrt (E a) + ∫ t in a..b, force t))) := by
    simpa only [add_zero] using tendsto_const_nhds.mul
      (((tendsto_const_nhds.add ht0).sqrt).add tendsto_const_nhds)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with eta heta
  exact regularized_sqrt_energy_gronwall hab hEcont hderiv hE hforce hforcepos hC heta hineq

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MovingSlabEnergy
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem point_mem_shrinkingSlab {xl xr a b speed x t : ℝ}
    (ht : t ∈ Icc a b)
    (hx : x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t)) :
    coordinatePoint x t ∈ shrinkingSlab xl xr a b speed := by
  simpa [shrinkingSlab, coordinatePoint] using And.intro ht hx

theorem shrinkingSlab_subset_rectangle
    {xl xr a b speed radius lo hi : ℝ} (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hxl : -radius < xl) (hxr : xr < radius)
    (ha : a ∈ Ioo lo hi) (hb : b ∈ Ioo lo hi)
    (hlength : 2 * speed * (b - a) < xr - xl) :
    shrinkingSlab xl xr a b speed ⊆ coordinateRectangle radius lo hi := by
  intro p hp
  have hgeo := inward_interval_geometry hab hspeed hxl hxr hlength hp.1
  exact ⟨⟨hgeo.1.1.trans_le hp.2.1, hp.2.2.trans_lt hgeo.2.1.2⟩,
    ⟨ha.1.trans_le hp.1.1, hp.1.2.trans_lt hb.2⟩⟩

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MovingIntervalSobolev
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

def spatialJet (f : Coord → ℝ) : ℕ → Coord → ℝ
  | 0 => f
  | n + 1 => coordPartial 0 (spatialJet f n)

theorem spatialJet_contDiffOn {f : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) :
    ContDiffOn ℝ ∞ (spatialJet f n) U := by
  induction n with
  | zero => exact hf
  | succ n hn => exact partial_contDiffOn hn hU 0

theorem smooth_slice_memLp_two
    {f : Coord → ℝ} {U : Set Coord} {left right theta : ℝ}
    (hf : ContinuousOn f U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U) :
    MemLp (fun x => f (coordinatePoint x theta)) 2 (volume.restrict (Icc left right)) := by
  have hc : ContinuousOn (fun x => f (coordinatePoint x theta)) (Icc left right) :=
    hf.comp (by unfold coordinatePoint; fun_prop) hseg
  exact (memLp_two_iff_integrable_sq (hc.aestronglyMeasurable measurableSet_Icc)).2
    ((hc.pow 2).integrableOn_compact isCompact_Icc)

theorem interval_square_integral_le_of_eLpNorm
    {f : ℝ → ℝ} {left right : ℝ} {H : ℝ≥0} (hlr : left ≤ right)
    (hf : MemLp f 2 (volume.restrict (Icc left right)))
    (hH : eLpNorm f 2 (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞)) :
    (∫ x in left..right, f x ^ 2) ≤ (H : ℝ) ^ 2 := by
  rw [intervalIntegral.integral_of_le hlr, restrict_Ioc_eq_restrict_Icc,
    integral_square_eq_L2_norm_square hf, Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp]
  have hh := ENNReal.toReal_mono (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (H : ℝ≥0∞) ≠ ⊤) hH
  change (eLpNorm f 2 (volume.restrict (Icc left right))).toReal ≤ (H : ℝ) at hh
  exact (sq_le_sq₀ ENNReal.toReal_nonneg H.2).2 hh

def SpatialSliceL2Bound {ι : Type*} (F : ι → Coord → ℝ) (theta left right : ℝ)
    (N : ℕ) (H : ℝ≥0) : Prop :=
  ∀ i n, n ≤ N → eLpNorm (fun x => spatialJet (F i) n (coordinatePoint x theta)) 2
    (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞)

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MovingIntervalSourceL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators ENNReal NNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Analytic

theorem spatialProductL2Budget_lt_top (lengthFloor left right : ℝ) (H : ℝ≥0) (n : ℕ) :
    spatialProductL2Budget lengthFloor left right H n < (⊤ : ℝ≥0∞) := by
  unfold spatialProductL2Budget
  rw [Real.volume_Icc]
  finiteness

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_MovingFirstJetBase
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal NNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

def spatialFirstJet (z : Coord → ℝ) (i : Fin 2) : Coord → ℝ := coordPartial i z

theorem spatialJet_firstJet_eq_word (z : Coord → ℝ) (n : ℕ) (i : Fin 2) :
    spatialJet (spatialFirstJet z i) n =
      iteratedCoordPartial (List.replicate n 0 ++ [i]) z := by
  induction n with
  | zero => rfl
  | succ n hn =>
      simp only [spatialJet, List.replicate_succ, List.cons_append, iteratedCoordPartial, hn]

theorem coordinateBound_spatialFirstJet
    {z : Coord → ℝ} {V : Set Coord} {N n : ℕ} {Z : ℝ}
    (hz : CoordinateBound z V (N + 1) Z) (hn : n ≤ N) (i : Fin 2) {p : Coord} (hp : p ∈ V) :
    |spatialJet (spatialFirstJet z i) n p| ≤ Z := by
  rw [spatialJet_firstJet_eq_word]
  apply hz _ _ p hp
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  omega

theorem coordinateBound_to_spatialFirstJet_L2
    {z : Coord → ℝ} {V : Set Coord} {theta left right Z widthUpper : ℝ} {N : ℕ}
    (hz : CoordinateBound z V (N + 1) Z) (hZ : 0 ≤ Z)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ V)
    (hwidth : right - left ≤ widthUpper) :
    SpatialSliceL2Bound (spatialFirstJet z) theta left right N
      (firstJetSliceBudget Z widthUpper) := by
  intro i n hn
  have hmeas : Measurable (spatialJet (spatialFirstJet z i) n) := by
    cases n with
    | zero => exact measurable_fderiv_apply_const ℝ z (Pi.single i 1)
    | succ order =>
        exact measurable_fderiv_apply_const ℝ
          (spatialJet (spatialFirstJet z i) order) (Pi.single 0 1)
  have hpoint : Continuous (fun x : ℝ => coordinatePoint x theta) := by
    unfold coordinatePoint
    fun_prop
  have hdom : ∀ᵐ x ∂volume.restrict (Icc left right),
      ‖spatialJet (spatialFirstJet z i) n (coordinatePoint x theta)‖ ≤ ‖Z‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hZ]
    exact coordinateBound_spatialFirstJet hz hn i (hseg x hx)
  have hvol : volume (Icc left right) ≤ ENNReal.ofReal widthUpper := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal hwidth
  calc
    _ ≤ eLpNorm (fun _ : ℝ => Z) 2 (volume.restrict (Icc left right)) :=
      eLpNorm_mono_ae hdom
    _ = ‖Z‖ₑ * (volume (Icc left right)) ^ (1 / (2 : ℝ)) := by
      rw [eLpNorm_const' Z (by norm_num) (by norm_num)]
      simp only [Measure.restrict_apply_univ, ENNReal.toReal_ofNat]
    _ ≤ ‖Z‖ₑ * (ENNReal.ofReal widthUpper) ^ (1 / (2 : ℝ)) :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hvol (by norm_num))
    _ = _ := (firstJetSliceBudget_coe Z widthUpper).symm

theorem coordinateC8_to_spatialFirstJet_L2_seven
    {z : Coord → ℝ} {V : Set Coord} {theta left right Z widthUpper : ℝ}
    (hz : CoordinateBound z V 8 Z) (hZ : 0 ≤ Z)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ V)
    (hwidth : right - left ≤ widthUpper) :
    SpatialSliceL2Bound (spatialFirstJet z) theta left right 7
      (firstJetSliceBudget Z widthUpper) :=
  coordinateBound_to_spatialFirstJet_L2 hz hZ hseg hwidth

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_HorizontalJetCalculus
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

def horizontalJet {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Coord → V) : ℕ → Coord → V
  | 0 => f
  | n + 1 => coordPartial 0 (horizontalJet f n)

theorem horizontalJet_eq_spatialJet (f : Coord → ℝ) (n : ℕ) :
    horizontalJet f n = spatialJet f n := by
  induction n with
  | zero => rfl
  | succ n hn => simp only [horizontalJet, spatialJet, hn]

theorem horizontalPoint_contDiff (y : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ => coordinatePoint x y) := by
  unfold coordinatePoint
  fun_prop

end SmoothLocal.HighEquation

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

theorem coordinateSwapMatrix_isUnit : IsUnit coordinateSwapMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det, coordinateSwapMatrix_det]
  exact isUnit_neg_one

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_SwappedDarboux
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def jetXX (g : MetricField) (p : Coord) (c : ℝ) (u : Coord) : ℝ :=
  c - jetConnection g p 0 0 u

def solvedDarbouxQ (g : MetricField) (p : Coord) (b c : ℝ) (u : Coord) : ℝ :=
  jetConnection g p 1 1 u + jetNumerator g p b u / jetXX g p c u

theorem jetEnergy_swappedMetric (g : MetricField) (p u : Coord) :
    jetEnergy (swappedMetric g) p (coordinateSwap u) =
      jetEnergy g (coordinateSwap p) u := by
  simp only [jetEnergy, swappedMetric_det, swappedMetric_apply, coordinateSwap_apply,
    swapCoordinateIndex_zero, swapCoordinateIndex_one]
  ring

theorem solvedDarbouxQ_deriv_b (g : MetricField) (p u : Coord) (b c : ℝ)
    (_hne : jetXX g p c u ≠ 0) :
    deriv (fun t => solvedDarbouxQ g p t c u) b =
      2 * (jetMixed g p b u / jetXX g p c u) := by
  have hd := (((((hasDerivAt_id b).sub_const (jetConnection g p 0 1 u)).pow 2).add_const
    (gaussianCurvature g p * jetEnergy g p u)).div_const (jetXX g p c u)).const_add
      (jetConnection g p 1 1 u)
  simp only [Pi.pow_apply, id_eq] at hd
  change deriv (fun t => jetConnection g p 1 1 u +
    ((t - jetConnection g p 0 1 u) ^ 2 + gaussianCurvature g p * jetEnergy g p u) /
      jetXX g p c u) b = _
  rw [hd.deriv]
  simp only [jetMixed, mul_one]
  ring

theorem solvedDarbouxQ_deriv_c (g : MetricField) (p u : Coord) (b c : ℝ)
    (hne : jetXX g p c u ≠ 0) :
    deriv (fun t => solvedDarbouxQ g p b t u) c =
      -((jetMixed g p b u / jetXX g p c u) ^ 2 +
        gaussianCurvature g p * jetEnergy g p u / (jetXX g p c u) ^ 2) := by
  have hdH := (hasDerivAt_id c).sub_const (jetConnection g p 0 0 u)
  have hd := ((hasDerivAt_const c (jetNumerator g p b u)).div hdH hne).const_add
    (jetConnection g p 1 1 u)
  simp only [Pi.div_apply, id_eq] at hd
  change deriv (fun t => jetConnection g p 1 1 u +
    jetNumerator g p b u / (t - jetConnection g p 0 0 u)) c = _
  rw [hd.deriv]
  change (0 * jetXX g p c u - jetNumerator g p b u * 1) / (jetXX g p c u) ^ 2 = _
  simp only [jetNumerator]
  field_simp [hne]
  ring

theorem jetXX_at_height (g : MetricField) (p : Coord) (z : Coord → ℝ) :
    jetXX g p (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p) =
      covHessian g z p 0 0 := rfl

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_SixVariableQ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem qToPState_contDiff : ContDiff ℝ ∞ qToPState := qToPStateCLM.contDiff

@[simp] theorem qToPState_four (w : DarbouxState) : qToPState w 4 = w 4 := rfl
@[simp] theorem qToPState_five (w : DarbouxState) : qToPState w 5 = w 5 := rfl

def stateQDenominator (g : MetricField) (w : DarbouxState) : ℝ :=
  jetXX g (statePoint w) (w 5) (stateGradient w)

def darbouxQStateDomain (g : MetricField) (U : Set Coord) : Set DarbouxState :=
  {w | statePoint w ∈ U ∧ stateQDenominator g w ≠ 0}

def sixVariableQ (g : MetricField) : DarbouxState → ℝ :=
  sixVariableP (swappedMetric g) ∘ qToPState

def qSolutionJet (z : Coord → ℝ) (p : Coord) : DarbouxState :=
  ![p 0, p 1, coordPartial 0 z p, coordPartial 1 z p,
    coordPartial 0 (coordPartial 1 z) p, coordPartial 0 (coordPartial 0 z) p]

theorem statePoint_qSolutionJet (z : Coord → ℝ) (p : Coord) :
    statePoint (qSolutionJet z p) = p := by
  ext i
  fin_cases i <;> rfl

theorem stateGradient_qSolutionJet (z : Coord → ℝ) (p : Coord) :
    stateGradient (qSolutionJet z p) = fun i => coordPartial i z p := by
  ext i
  fin_cases i <;> rfl

theorem stateQDenominator_qSolutionJet (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    stateQDenominator g (qSolutionJet z p) = covHessian g z p 0 0 := by
  unfold stateQDenominator
  rw [statePoint_qSolutionJet, stateGradient_qSolutionJet]
  exact jetXX_at_height g p z

theorem qSolutionJet_mem_domain {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    qSolutionJet z p ∈ darbouxQStateDomain g U := by
  constructor
  · simpa only [statePoint_qSolutionJet] using hp
  · simpa only [stateQDenominator_qSolutionJet] using hxx

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QPrincipal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def qFirstCoefficient (g : MetricField) (i : Fin 6) (w : DarbouxState) : ℝ :=
  fderiv ℝ (sixVariableQ g) w (Pi.single i 1)

end SmoothLocal.HighEquation

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

def metricFirstJet (g : MetricField) (p : Coord) : MetricFirstJet :=
  fun d i j => coordPartial d (fun q => g q i j) p

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseProfiles
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearMatrix_det
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

def shearCoordinates (q0 : ℝ) (p : Coord) : Coord := ![p 0, p 1 + q0 * p 0]
def inverseShearCoordinates (q0 : ℝ) (p : Coord) : Coord := ![p 0, p 1 - q0 * p 0]
def thetaCovector (q0 : ℝ) : Coord := ![q0, 1]

theorem shearCoordinates_contDiff (q0 : ℝ) : ContDiff ℝ ∞ (shearCoordinates q0) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : Coord => x 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : Coord => x 1 + q0 * x 0)
    fun_prop

theorem inverseShearCoordinates_contDiff (q0 : ℝ) : ContDiff ℝ ∞ (inverseShearCoordinates q0) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : Coord => x 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : Coord => x 1 - q0 * x 0)
    fun_prop

theorem inverse_shear (q0 : ℝ) (p : Coord) :
    inverseShearCoordinates q0 (shearCoordinates q0 p) = p := by
  ext i
  fin_cases i <;> simp [shearCoordinates, inverseShearCoordinates]

theorem inverseShearCoordinates_eq_affine (q0 : ℝ) :
    inverseShearCoordinates q0 = affineCoordinates 0 (inverseShearMatrix q0) := by
  ext p i
  fin_cases i <;> simp [inverseShearCoordinates, inverseShearMatrix,
    affineCoordinates, dotProduct, Fin.sum_univ_two]
  ring

def pulseScalar (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) : ℝ :=
  (1 / tau ^ N) * axisBump a (p 0) * temporalCutoff (tau * p 1 / delta) *
    Real.cos (tau * p 0)

def pulseTensor (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) : MetricField := fun p i j =>
  pulseScalar a N delta tau (shearCoordinates q0 p) * thetaCovector q0 i * thetaCovector q0 j

def testMetric (gStar : MetricField) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) : MetricField :=
  gStar + pulseTensor q0 a N delta tau

theorem pulseScalar_contDiff (a : ℝ) (N : ℕ) (delta tau : ℝ) :
    ContDiff ℝ ∞ (pulseScalar a N delta tau) := by
  unfold pulseScalar temporalCutoff
  exact ((contDiff_const.mul ((axisBump_contDiff a).comp (contDiff_apply ℝ ℝ 0))).mul
    ((axisBump_contDiff (1 / 2)).comp
      ((contDiff_const.mul (contDiff_apply ℝ ℝ 1)).div_const delta))).mul
    (Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0)))

theorem pulseTensor_contDiff (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) :
    ContDiff ℝ ∞ (pulseTensor q0 a N delta tau) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (((pulseScalar_contDiff a N delta tau).comp (shearCoordinates_contDiff q0)).mul
    contDiff_const).mul contDiff_const

theorem pulseTensor_symmetric (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) (i j : Fin 2) :
    pulseTensor q0 a N delta tau p i j = pulseTensor q0 a N delta tau p j i := by
  unfold pulseTensor
  ring

def pulseLocalBox (a delta tau : ℝ) : Set Coord :=
  Icc (![-a, -(delta / (2 * tau))]) (![a, delta / (2 * tau)])

def pulseOriginalBox (q0 a delta tau : ℝ) : Set Coord :=
  inverseShearCoordinates q0 '' pulseLocalBox a delta tau

theorem pulseLocalBox_isCompact (a delta tau : ℝ) : IsCompact (pulseLocalBox a delta tau) :=
  isCompact_Icc

theorem pulseOriginalBox_isCompact (q0 a delta tau : ℝ) :
    IsCompact (pulseOriginalBox q0 a delta tau) :=
  (pulseLocalBox_isCompact a delta tau).image (inverseShearCoordinates_contDiff q0).continuous

theorem pulseScalar_support_bound {a delta tau : ℝ} (ha : 0 < a)
    (hd : 0 < delta) (ht : 0 < tau) (N : ℕ) {p : Coord}
    (hp : pulseScalar a N delta tau p ≠ 0) : p ∈ pulseLocalBox a delta tau := by
  have hχ : axisBump a (p 0) ≠ 0 := by
    intro h
    apply hp
    simp only [pulseScalar, h, mul_zero, zero_mul]
  have hφ : temporalCutoff (tau * p 1 / delta) ≠ 0 := by
    intro h
    apply hp
    simp only [pulseScalar, h, mul_zero, zero_mul]
  have hx := abs_lt.mp (axisBump_support_bound ha hχ)
  have hy := axisBump_support_bound (by norm_num : (0 : ℝ) < 1 / 2) hφ
  have hy' : |p 1| < delta / (2 * tau) := by
    rw [abs_div, abs_mul, abs_of_pos ht, abs_of_pos hd] at hy
    apply (lt_div_iff₀ (mul_pos (by norm_num) ht)).mpr
    have hh := (div_lt_iff₀ hd).mp hy
    nlinarith
  constructor <;> intro i <;> fin_cases i
  · exact hx.1.le
  · exact (abs_lt.mp hy').1.le
  · exact hx.2.le
  · exact (abs_lt.mp hy').2.le

theorem pulseTensor_tsupport_subset {q0 a delta tau : ℝ}
    (ha : 0 < a) (hd : 0 < delta) (ht : 0 < tau) (N : ℕ) :
    tsupport (pulseTensor q0 a N delta tau) ⊆ pulseOriginalBox q0 a delta tau := by
  apply closure_minimal _ (pulseOriginalBox_isCompact q0 a delta tau).isClosed
  intro p hp
  have hs : pulseScalar a N delta tau (shearCoordinates q0 p) ≠ 0 := by
    intro h
    apply hp
    ext i j
    simp only [pulseTensor, h, zero_mul, Matrix.zero_apply]
  exact ⟨shearCoordinates q0 p, pulseScalar_support_bound ha hd ht N hs, inverse_shear q0 p⟩

theorem pulseOriginalBox_subset_patchBox {q0 a delta tau : ℝ}
    (ha : a ≤ 1 / 10) (hy : delta / (2 * tau) + |q0| * a ≤ 1 / 10) :
    pulseOriginalBox q0 a delta tau ⊆ patchBox := by
  rintro p ⟨u, hu, rfl⟩
  have hu0 : |u 0| ≤ a := abs_le.mpr ⟨hu.1 0, hu.2 0⟩
  have hu1 : |u 1| ≤ delta / (2 * tau) := abs_le.mpr ⟨hu.1 1, hu.2 1⟩
  have h0 : |inverseShearCoordinates q0 u 0| ≤ 1 / 10 := hu0.trans ha
  have h1 : |inverseShearCoordinates q0 u 1| ≤ 1 / 10 := by
    change |u 1 - q0 * u 0| ≤ _
    calc
      _ ≤ |u 1| + |q0 * u 0| := abs_sub _ _
      _ = |u 1| + |q0| * |u 0| := by rw [abs_mul]
      _ ≤ delta / (2 * tau) + |q0| * a :=
        add_le_add hu1 (mul_le_mul_of_nonneg_left hu0 (abs_nonneg q0))
      _ ≤ _ := hy
  constructor <;> intro i <;> fin_cases i
  · exact (abs_le.mp h0).1
  · exact (abs_le.mp h1).1
  · exact (abs_le.mp h0).2
  · exact (abs_le.mp h1).2

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseCurvaturePrincipal
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

def metricInShearCoordinates (g : MetricField) (q0 : ℝ) : MetricField :=
  affinePullbackMetric g 0 (inverseShearMatrix q0)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_ActualShearHeight
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

def heightInShearCoordinates (z : Coord → ℝ) (q0 : ℝ) : Coord → ℝ :=
  z ∘ inverseShearCoordinates q0

theorem heightInShearCoordinates_contDiffOn {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (q0 : ℝ) :
    ContDiffOn ℝ ∞ (heightInShearCoordinates z q0) (inverseShearCoordinates q0 ⁻¹' U) :=
  hz.comp (inverseShearCoordinates_contDiff q0).contDiffOn (fun _ hp => hp)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_ShearHeightJets
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
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

def inverseShearCLM (q0 : ℝ) : Coord →L[ℝ] Coord :=
  LinearMap.toContinuousLinearMap
    { toFun := inverseShearCoordinates q0
      map_add' := by
        intro left right
        ext index
        fin_cases index
        · rfl
        · dsimp [inverseShearCoordinates]
          ring
      map_smul' := by
        intro scalar point
        ext index
        fin_cases index
        · rfl
        · dsimp [inverseShearCoordinates]
          ring }

@[simp] theorem inverseShearCLM_apply (q0 : ℝ) (p : Coord) :
    inverseShearCLM q0 p = inverseShearCoordinates q0 p := rfl

theorem inverseShearCLM_norm_le (q0 : ℝ) : ‖inverseShearCLM q0‖ ≤ 1 + |q0| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (1 + |q0|) * ‖v‖)).mpr
  intro i
  fin_cases i
  · change ‖v 0‖ ≤ _
    exact (norm_le_pi_norm v 0).trans (by nlinarith [mul_nonneg (abs_nonneg q0) (norm_nonneg v)])
  · change ‖v 1 - q0 * v 0‖ ≤ _
    calc
      _ ≤ ‖v 1‖ + ‖q0 * v 0‖ := norm_sub_le _ _
      _ = ‖v 1‖ + |q0| * ‖v 0‖ := by rw [norm_mul, Real.norm_eq_abs q0]
      _ ≤ ‖v‖ + |q0| * ‖v‖ := add_le_add (norm_le_pi_norm v 1)
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm v 0) (abs_nonneg q0))
      _ = _ := by ring

theorem local_linear_full_jet_norm_bound {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (L : Coord →L[ℝ] Coord)
    {p : Coord} (hp : L p ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ L) p‖ ≤ ‖iteratedFDeriv ℝ n f (L p)‖ * ‖L‖^n := by
  have hpre := hU.preimage L.continuous
  have heq := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hp
    (i := n) (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen n hpre hp,
    iteratedFDerivWithin_of_isOpen n hU hp] at heq
  rw [heq]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ n f (L p)) (fun _ : Fin n => L)

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

theorem metricInShearCoordinates_four_terms (g : MetricField) (q0 : ℝ) (i j : Fin 2) :
    (fun p => metricInShearCoordinates g q0 p i j) =
      (fun p =>
        ((inverseShearMatrix q0 0 i * inverseShearMatrix q0 0 j) *
            heightInShearCoordinates (fun r => g r 0 0) q0 p +
          (inverseShearMatrix q0 0 i * inverseShearMatrix q0 1 j) *
            heightInShearCoordinates (fun r => g r 0 1) q0 p) +
        ((inverseShearMatrix q0 1 i * inverseShearMatrix q0 0 j) *
            heightInShearCoordinates (fun r => g r 1 0) q0 p +
          (inverseShearMatrix q0 1 i * inverseShearMatrix q0 1 j) *
            heightInShearCoordinates (fun r => g r 1 1) q0 p)) := by
  funext p
  simp only [metricInShearCoordinates, affinePullbackMetric, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_two, heightInShearCoordinates,
    Function.comp_apply, ← inverseShearCoordinates_eq_affine]
  ring

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_StateJetSegment
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_five _root_.OAI.SmoothLocal.HighEquation.qToPState_four _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def stateSegment (w0 w1 : DarbouxState) (sigma : ℝ) : DarbouxState :=
  (1 - sigma) • w0 + sigma • w1

theorem statePoint_segment {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) (sigma : ℝ) :
    statePoint (stateSegment w0 w1 sigma) = statePoint w0 := by
  have h0 : w0 0 = w1 0 := congrFun hp 0
  have h1 : w0 1 = w1 1 := congrFun hp 1
  ext i
  fin_cases i <;> simp [statePoint, stateSegment, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ← h0, ← h1] <;> ring

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

def stateBaseCompact (S : Set Coord) (M : ℝ) : Set DarbouxState :=
  (statePoint ⁻¹' S) ∩ Icc (fun _ => -M) (fun _ => M)

theorem stateSegment_coord_bound {w0 w1 : DarbouxState} {sigma M : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ i, |w0 i| ≤ M) (h1 : ∀ i, |w1 i| ≤ M) (i : Fin 6) :
    |stateSegment w0 w1 sigma i| ≤ M := by
  change |(1 - sigma) * w0 i + sigma * w1 i| ≤ M
  calc
    _ ≤ |(1 - sigma) * w0 i| + |sigma * w1 i| := abs_add_le _ _
    _ = (1 - sigma) * |w0 i| + sigma * |w1 i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2), abs_of_nonneg hs.1]
    _ ≤ (1 - sigma) * M + sigma * M :=
      add_le_add (mul_le_mul_of_nonneg_left (h0 i) (sub_nonneg.mpr hs.2))
        (mul_le_mul_of_nonneg_left (h1 i) hs.1)
    _ = M := by ring

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseFlowDistance
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem scalar_fderiv_coordinate_bound {q : Coord → ℝ} {p v : Coord} {M : ℝ}
    (_hM : 0 ≤ M) (hpartial : ∀ i : Fin 2, |coordPartial i q p| ≤ M) :
    |fderiv ℝ q p v| ≤ M*(|v 0|+|v 1|) := by
  have he : v = (v 0) • Pi.single 0 (1 : ℝ) + (v 1) • Pi.single 1 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [he, map_add, map_smul, map_smul]
  change |v 0 * coordPartial 0 q p + v 1 * coordPartial 1 q p| ≤ _
  calc
    _ ≤ |v 0 * coordPartial 0 q p| + |v 1 * coordPartial 1 q p| := abs_add_le _ _
    _ = |v 0| * |coordPartial 0 q p|+|v 1| * |coordPartial 1 q p| := by rw [abs_mul,abs_mul]
    _ ≤ |v 0| * M+|v 1| * M := add_le_add
      (mul_le_mul_of_nonneg_left (hpartial 0) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hpartial 1) (abs_nonneg _))
    _ = _ := by ring

theorem quotient_change_from_origin
    {q : Coord → ℝ} {U : Set Coord} {M : ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) (hM : 0 ≤ M)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    {p : Coord} (hp : p ∈ modelSquare) : |q p-q 0| ≤ M*(|p 0|+|p 1|) := by
  have hz : (0 : Coord) ∈ modelSquare := by constructor <;> intro i <;> norm_num
  have hconv : Convex ℝ modelSquare := convex_Icc _ _
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • p ∈ modelSquare := by
    have h := hconv hp hz ht.1 (sub_nonneg.mpr ht.2) (by ring)
    simpa only [smul_zero, add_zero] using h
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => q (s • p)) (fderiv ℝ q (t • p) p) t := by
    have hdq := ((hq.contDiffAt (hU.mem_nhds (hSU (hseg t ht)))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
    have hdp : HasDerivAt (fun s : ℝ => s • p) p t := by
      have ht := (hasDerivAt_id t).smul_const p
      change HasDerivAt (fun s : ℝ => s • p) ((1 : ℝ) • p) t at ht
      rw [one_smul] at ht
      exact ht
    exact hdq.comp_hasDerivAt t hdp
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖deriv (fun s : ℝ => q (s • p)) t‖ ≤ M*(|p 0|+|p 1|) := by
    rw [(hder t ht).deriv, Real.norm_eq_abs]
    exact scalar_fderiv_coordinate_bound hM (hpartial (t • p) (hseg t ht))
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hder t ht).differentiableAt) hb
    (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  simpa only [zero_smul, one_smul, sub_zero, norm_one, mul_one, Real.norm_eq_abs] using h

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem flow_segment_coordinate_sum
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {q0 T r s t u : ℝ} (hq0 : |q0| ≤ 1/20) (_hT : 0 < T) (hT2 : T < 2)
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Icc (-T) T) (hu : u ∈ Icc (-T) T)
    (htheta : |Y s t+q0*t| ≤ r) :
    |u|+|Y s u| ≤ r+107*T/100 := by
  have ht' : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hu' : u ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have habst : |t| ≤ T := abs_le.mpr ht
  have habsu : |u| ≤ T := abs_le.mpr hu
  have hdt : |u-t| ≤ 2*T := (abs_sub u t).trans (by linarith)
  have hmove := (cap_flow_time_lipschitz hq hU hSU hY hrange hstart hode hsmall hs ht' hu').trans
    (mul_le_mul_of_nonneg_left hdt (by norm_num : (0 : ℝ) ≤ 1/100))
  have hprod : |q0*t| ≤ (1/20)*T := by
    rw [abs_mul]
    exact mul_le_mul hq0 habst (abs_nonneg _) (by norm_num)
  have hyt : |Y s t| ≤ r+(1/20)*T := by
    calc
      |Y s t| = |(Y s t+q0*t)-q0*t| := by congr 1; ring
      _ ≤ |Y s t+q0*t|+|q0*t| := abs_sub _ _
      _ ≤ _ := add_le_add htheta hprod
  have hyu : |Y s u| ≤ |Y s u-Y s t|+|Y s t| := by
    calc
      |Y s u| = |(Y s u-Y s t)+Y s t| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  linarith

theorem flow_segment_quotient_near_center
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {M q0 L T r s t : ℝ} (hM : 0 ≤ M) (hL : 0 < L)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    (hq0 : |q0| ≤ 1/20) (hcenter : |q 0-q0| ≤ 1/(100*L))
    (hT : 0 < T) (hT2 : T < 2) (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Icc (-T) T)
    (htheta : |Y s t+q0*t| ≤ r)
    (hrsmall : M*(r+107*T/100) ≤ 9/(100*L)) :
    ∀ u ∈ Icc (-T) T, |q (coordinatePoint u (Y s u))-q0| ≤ 1/(10*L) := by
  intro u hu
  have hu2 : u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hp : coordinatePoint u (Y s u) ∈ modelSquare := coordinatePoint_mem_modelSquare
    ⟨by linarith [hu2.1],by linarith [hu2.2]⟩
    (hrange s ⟨hs.1.le,hs.2.le⟩ u hu2)
  have hnorm := flow_segment_coordinate_sum hq hU hSU hY hrange hstart hode
    hsmall hq0 hT hT2 hs ht hu htheta
  have hlocal : |q (coordinatePoint u (Y s u))-q 0| ≤ M*(|u|+|Y s u|) := by
    simpa [coordinatePoint] using quotient_change_from_origin hq hU hSU hM hpartial hp
  have hsum : |q (coordinatePoint u (Y s u))-q0| ≤
      |q (coordinatePoint u (Y s u))-q 0|+|q 0-q0| := by
    calc
      _ = |(q (coordinatePoint u (Y s u))-q 0)+(q 0-q0)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have ha := hsum.trans (add_le_add (hlocal.trans
    (mul_le_mul_of_nonneg_left hnorm hM)) hcenter)
  have heq : 9/(100*L)+1/(100*L) = 1/(10*L) := by field_simp [hL.ne'] <;> ring
  exact ha.trans ((add_le_add hrsmall le_rfl).trans_eq heq)

theorem actual_shear_seed_distance
    {q0 epsilon T s t : ℝ} (hT : 0 < T) (hT2 : T < 2)
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Icc (-T) T)
    (hclose : ∀ u ∈ Icc (-T) T, |q (coordinatePoint u (Y s u))-q0| ≤ epsilon) :
    |Y s t+q0*t-s| ≤ epsilon*|t| := by
  have hd (u : ℝ) (hu : u ∈ Icc (-T) T) :
      HasDerivAt (fun a => Y s a+q0*a) (-q (coordinatePoint u (Y s u))+q0) u := by
    have hu2 : u ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have hh := (cap_flow_time_hasDerivAt hq hU hSU hY hrange hstart hode hs hu2).add
      ((hasDerivAt_id u).const_mul q0)
    change HasDerivAt (fun a : ℝ => Y s a + q0 * a)
      (-q (coordinatePoint u (Y s u)) + q0 * 1) u at hh
    rw [mul_one] at hh
    exact hh
  have hb (u : ℝ) (hu : u ∈ Icc (-T) T) :
      ‖deriv (fun a => Y s a+q0*a) u‖ ≤ epsilon := by
    rw [(hd u hu).deriv, Real.norm_eq_abs]
    have heq : -q (coordinatePoint u (Y s u))+q0 = -(q (coordinatePoint u (Y s u))-q0) := by ring
    rw [heq,abs_neg]
    exact hclose u hu
  have h := (convex_Icc (-T) T).norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (hd u hu).differentiableAt) hb
    (show (0 : ℝ) ∈ Icc (-T) T by constructor <;> linarith) ht
  simpa only [hstart s ⟨hs.1.le,hs.2.le⟩, mul_zero, add_zero, sub_zero, Real.norm_eq_abs] using h

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseDerivativeBounds
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

def xiCLM : Coord →L[ℝ] ℝ := ContinuousLinearMap.proj 0
def thetaCLM (q0 : ℝ) : Coord →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 1 + q0 • ContinuousLinearMap.proj 0

def pulseScaleBound (q0 delta : ℝ) : ℝ :=
  1 + ‖xiCLM‖ + |delta⁻¹| * ‖thetaCLM q0‖

theorem pulseScaleBound_pos (q0 delta : ℝ) : 0 < pulseScaleBound q0 delta := by
  unfold pulseScaleBound
  positivity

theorem pulseScaleBound_xi (q0 delta : ℝ) : ‖xiCLM‖ ≤ pulseScaleBound q0 delta := by
  have h := mul_nonneg (abs_nonneg delta⁻¹) (norm_nonneg (thetaCLM q0))
  unfold pulseScaleBound
  linarith

theorem pulseScaleBound_theta (q0 delta : ℝ) :
    |delta⁻¹| * ‖thetaCLM q0‖ ≤ pulseScaleBound q0 delta := by
  unfold pulseScaleBound
  linarith [norm_nonneg xiCLM]

theorem norm_scaled_theta_le (q0 delta : ℝ) {tau : ℝ} (ht : 0 ≤ tau) :
    ‖(tau / delta) • thetaCLM q0‖ ≤ tau * pulseScaleBound q0 delta := by
  rw [norm_smul, Real.norm_eq_abs, div_eq_mul_inv, abs_mul, abs_of_nonneg ht]
  calc
    _ = tau * (|delta⁻¹| * ‖thetaCLM q0‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pulseScaleBound_theta q0 delta) ht

theorem norm_scaled_xi_le (q0 delta : ℝ) {tau : ℝ} (ht : 0 ≤ tau) :
    ‖tau • xiCLM‖ ≤ tau * pulseScaleBound q0 delta := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  exact mul_le_mul_of_nonneg_left (pulseScaleBound_xi q0 delta) ht

theorem linear_comp_derivative_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : Coord →L[ℝ] ℝ) (k : ℕ) (p : Coord) {C s : ℝ}
    (hC : 0 ≤ C) (hfC : ∀ t, ‖iteratedFDeriv ℝ k f t‖ ≤ C)
    (hL : ‖L‖ ≤ s) :
    ‖iteratedFDeriv ℝ k (f ∘ L) p‖ ≤ C * s ^ k := by
  rw [L.iteratedFDeriv_comp_right hf p (WithTop.coe_le_coe.mpr le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (L p)‖ * ∏ _ : Fin k, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ k f (L p)‖ * ‖L‖ ^ k := by simp
    _ ≤ C * s ^ k := mul_le_mul (hfC _) (pow_le_pow_left₀ (norm_nonneg L) hL k)
      (pow_nonneg (norm_nonneg L) k) hC

theorem product_derivative_bound {f g : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {A B : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k) (hB : ∀ k, 0 ≤ B k)
    {s : ℝ} (hs : 0 ≤ s)
    (hfa : ∀ k p, ‖iteratedFDeriv ℝ k f p‖ ≤ A k * s ^ k)
    (hgb : ∀ k p, ‖iteratedFDeriv ℝ k g p‖ ≤ B k * s ^ k) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (fun q => f q * g q) p‖ ≤ derivativeConvolution A B k * s ^ k := by
  refine (norm_iteratedFDeriv_mul_le hf hg p (WithTop.coe_le_coe.mpr le_top)).trans ?_
  rw [derivativeConvolution, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hpow : s ^ i * s ^ (k - i) = s ^ k := by
    rw [← pow_add, Nat.add_sub_of_le hik]
  calc
    _ ≤ (k.choose i : ℝ) * (A i * s ^ i) * (B (k - i) * s ^ (k - i)) :=
      mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfa i p) (Nat.cast_nonneg _)
          (mul_nonneg (hA i) (pow_nonneg hs i))) (hgb (k - i) p)
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg (hB (k - i)) (pow_nonneg hs (k - i)))
    _ = ((k.choose i : ℝ) * A i * B (k - i)) * s ^ k := by
      rw [← hpow]
      ring

def pulseCore (q0 a delta tau : ℝ) (p : Coord) : ℝ :=
  axisBump a (xiCLM p) * axisBump (1 / 2) (((tau / delta) • thetaCLM q0) p) *
    Real.cos ((tau • xiCLM) p)

theorem pulseCore_contDiff (q0 a delta tau : ℝ) : ContDiff ℝ ∞ (pulseCore q0 a delta tau) :=
  (((axisBump_contDiff a).comp_continuousLinearMap).mul
    ((axisBump_contDiff (1 / 2)).comp_continuousLinearMap)).mul
      Real.contDiff_cos.comp_continuousLinearMap

theorem pulseCore_derivative_le {a : ℝ} (ha : 0 < a) (q0 delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (pulseCore q0 a delta tau) p‖ ≤
      pulseCoreDerivativeBound a ha k * (tau * pulseScaleBound q0 delta) ^ k := by
  have ht0 : 0 ≤ tau := le_trans zero_le_one ht
  have hs : 0 ≤ tau * pulseScaleBound q0 delta :=
    mul_nonneg ht0 (pulseScaleBound_pos q0 delta).le
  have hxi : ‖xiCLM‖ ≤ tau * pulseScaleBound q0 delta :=
    (pulseScaleBound_xi q0 delta).trans
      (le_mul_of_one_le_left (pulseScaleBound_pos q0 delta).le ht)
  have hχ (j : ℕ) (p : Coord) :=
    linear_comp_derivative_bound (axisBump_contDiff a) xiCLM j p
      (axisBumpDerivativeBound_pos ha j).le (axisBump_derivative_le ha j) hxi
  have hφ (j : ℕ) (p : Coord) :=
    linear_comp_derivative_bound (axisBump_contDiff (1 / 2))
      ((tau / delta) • thetaCLM q0) j p
      (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ) < 1 / 2) j).le
      (axisBump_derivative_le (by norm_num : (0 : ℝ) < 1 / 2) j)
      (norm_scaled_theta_le q0 delta ht0)
  have hcos (j : ℕ) (p : Coord) :
      ‖iteratedFDeriv ℝ j (Real.cos ∘ (tau • xiCLM)) p‖ ≤
        1 * (tau * pulseScaleBound q0 delta) ^ j := by
    apply linear_comp_derivative_bound Real.contDiff_cos (tau • xiCLM) j p zero_le_one
    · intro t
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
        Real.abs_iteratedDeriv_cos_le_one j t
    · exact norm_scaled_xi_le q0 delta ht0
  have hχφ := product_derivative_bound
    (axisBump_contDiff a).comp_continuousLinearMap
    (axisBump_contDiff (1 / 2)).comp_continuousLinearMap
    (fun _ => (axisBumpDerivativeBound_pos ha _).le)
    (fun _ => (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ) < 1 / 2) _).le)
    hs hχ hφ
  exact product_derivative_bound
    ((axisBump_contDiff a).comp_continuousLinearMap.mul
      (axisBump_contDiff (1 / 2)).comp_continuousLinearMap)
    Real.contDiff_cos.comp_continuousLinearMap
    (derivativeConvolution_nonneg (fun _ => (axisBumpDerivativeBound_pos ha _).le)
      (fun _ => (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ) < 1 / 2) _).le))
    (fun _ => zero_le_one) hs hχφ hcos k p

def thetaTensor (q0 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  thetaCovector q0 i * thetaCovector q0 j

theorem pulseTensor_eq_core (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) :
    pulseTensor q0 a N delta tau = fun p =>
      (1 / tau ^ N) • (pulseCore q0 a delta tau p • thetaTensor q0) := by
  ext p i j
  simp only [pulseTensor, pulseScalar, pulseCore, shearCoordinates, thetaCLM, xiCLM,
    temporalCutoff, thetaTensor, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, Matrix.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have harg : tau / delta * (p 1 + q0 * p 0) = tau * (p 1 + q0 * p 0) / delta := by ring
  rw [harg]
  ring

def pulseDerivativeBound (q0 a : ℝ) (ha : 0 < a) (delta : ℝ) (k : ℕ) : ℝ :=
  ‖thetaTensor q0‖ * pulseCoreDerivativeBound a ha k * pulseScaleBound q0 delta ^ k

theorem pulseDerivativeBound_nonneg (q0 a : ℝ) (ha : 0 < a) (delta : ℝ) (k : ℕ) :
    0 ≤ pulseDerivativeBound q0 a ha delta k :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (pulseCoreDerivativeBound_nonneg ha k))
    (pow_nonneg (pulseScaleBound_pos q0 delta).le k)

theorem pulseTensor_derivative_le (q0 a : ℝ) (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (pulseTensor q0 a N delta tau) p‖ ≤
      pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N := by
  have ht0 : 0 < tau := lt_of_lt_of_le zero_lt_one ht
  let T : Fin 2 → Fin 2 → ℝ := thetaTensor q0
  let L := ContinuousLinearMap.toSpanSingleton ℝ T
  have hcore : ContDiff ℝ ∞ (pulseCore q0 a delta tau) := pulseCore_contDiff q0 a delta tau
  have hnorm := L.norm_iteratedFDeriv_comp_left hcore.contDiffAt
    (WithTop.coe_le_coe.mpr le_top) (n := k) (x := p)
  have hLnorm : ‖L‖ = ‖T‖ := ContinuousLinearMap.norm_toSpanSingleton (𝕜 := ℝ) T
  rw [hLnorm] at hnorm
  have hnorm' : ‖iteratedFDeriv ℝ k (L ∘ pulseCore q0 a delta tau) p‖ ≤
      ‖thetaTensor q0‖ * pulseCoreDerivativeBound a ha k * (tau * pulseScaleBound q0 delta) ^ k := by
    refine hnorm.trans ?_
    exact (mul_le_mul_of_nonneg_left (pulseCore_derivative_le ha q0 delta ht k p)
      (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm
  rw [pulseTensor_eq_core]
  change ‖iteratedFDeriv ℝ k (fun q => (1 / tau ^ N) • (L ∘ pulseCore q0 a delta tau) q) p‖ ≤ _
  have hsmul :
      iteratedFDeriv ℝ k (fun q => (1 / tau ^ N : ℝ) • (L ∘ pulseCore q0 a delta tau) q) p =
        (1 / tau ^ N : ℝ) • iteratedFDeriv ℝ k (L ∘ pulseCore q0 a delta tau) p :=
    iteratedFDeriv_const_smul_apply' (i := k) (a := (1 / tau ^ N : ℝ))
      ((L.contDiff.comp hcore).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  rw [hsmul,
    norm_smul, Real.norm_of_nonneg (div_nonneg zero_le_one (pow_nonneg ht0.le N))]
  calc
    _ ≤ (1 / tau ^ N) *
        (‖thetaTensor q0‖ * pulseCoreDerivativeBound a ha k * (tau * pulseScaleBound q0 delta) ^ k) :=
      mul_le_mul_of_nonneg_left hnorm' (div_nonneg zero_le_one (pow_nonneg ht0.le N))
    _ = _ := by rw [mul_pow]; unfold pulseDerivativeBound; ring

theorem fixed_order_pulse_bound_tendsto_zero (q0 a : ℝ) (ha : 0 < a)
    (delta : ℝ) (N k : ℕ) (hk : k < N) :
    Tendsto (fun tau : ℝ => pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N)
      atTop (𝓝 0) := by
  have hd : N - k ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hk)
  have h := (tendsto_inv_atTop_zero : Tendsto (fun tau : ℝ => tau⁻¹) atTop (𝓝 0)).pow (N - k)
  have h' : Tendsto (fun tau : ℝ => pulseDerivativeBound q0 a ha delta k * (tau⁻¹) ^ (N - k))
      atTop (𝓝 0) := by
    simpa only [zero_pow hd, mul_zero] using h.const_mul (pulseDerivativeBound q0 a ha delta k)
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau ht
  have htne : tau ≠ 0 := ht.ne'
  have hN : N = k + (N - k) := (Nat.add_sub_of_le hk.le).symm
  have hratio : tau ^ k / tau ^ N = (tau⁻¹) ^ (N - k) := by
    conv_lhs => rw [hN, pow_add]
    rw [inv_pow]
    field_simp
  simp only [mul_div_assoc, hratio]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseNeighborhood
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

theorem pulse_finite_derivative_bounds_eventually (q0 a : ℝ) (ha : 0 < a)
    (delta : ℝ) (N : ℕ) {epsilon : ℝ} (heps : 0 < epsilon) :
    ∀ᶠ tau : ℝ in atTop, ∀ k ∈ Finset.range N,
      pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N < epsilon := by
  apply (Finset.range N).eventually_all.mpr
  intro k hk
  exact (fixed_order_pulse_bound_tendsto_zero q0 a ha delta N k (Finset.mem_range.mp hk)).eventually_lt
    tendsto_const_nhds heps

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_PulseCapSeparation
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem pulseOriginalBox_coordinate_bounds {q0 a delta tau : ℝ} {p : Coord}
    (hp : p ∈ pulseOriginalBox q0 a delta tau) :
    |p 0| ≤ a ∧ |p 1+q0*p 0| ≤ delta/(2*tau) := by
  obtain ⟨v,hv,rfl⟩ := hp
  have hx : |v 0| ≤ a := abs_le.mpr
    ⟨by simpa [pulseLocalBox] using hv.1 0,by simpa [pulseLocalBox] using hv.2 0⟩
  have hy : |v 1| ≤ delta/(2*tau) := abs_le.mpr
    ⟨by simpa [pulseLocalBox] using hv.1 1,by simpa [pulseLocalBox] using hv.2 1⟩
  constructor
  · simpa [inverseShearCoordinates] using hx
  · have he : (inverseShearCoordinates q0 v) 1+q0*(inverseShearCoordinates q0 v) 0 = v 1 := by
      simp [inverseShearCoordinates]
    simpa only [he] using hy

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem pulseBox_seed_abs_lt_half
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {M q0 L r a delta tau : ℝ} (hM : 0 ≤ M) (hL : 0 < L) (hr : 0 < r)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    (hq0 : |q0| ≤ 1/20) (hcenter : |q 0-q0| ≤ 1/(100*L))
    (hT : L*r < 2) (ha : a ≤ L*r)
    (hrsmall : M*(r+107*(L*r)/100) ≤ 9/(100*L))
    (hwidth : delta/(2*tau) ≤ r/4)
    {p : Coord} (hp : p ∈ capChartDomain)
    (hpulse : capChart Y p ∈ pulseOriginalBox q0 a delta tau) :
    |p 1| < r/2 := by
  obtain ⟨hx,htheta⟩ := pulseOriginalBox_coordinate_bounds hpulse
  have htime : p 0 ∈ Icc (-(L*r)) (L*r) := by
    apply abs_le.mp
    exact (by simpa only [capChart_zero] using hx : |p 0| ≤ a).trans ha
  have htheta' : |Y (p 1) (p 0)+q0*p 0| ≤ delta/(2*tau) := by
    simpa only [capChart_one,capChart_zero,capFlowHeight] using htheta
  have hthetaR : |Y (p 1) (p 0)+q0*p 0| ≤ r := htheta'.trans (hwidth.trans (by linarith))
  have hclose := flow_segment_quotient_near_center hq hU hSU hY hrange hstart hode
    hsmall hM hL hpartial hq0 hcenter (mul_pos hL hr) hT hp.2 htime hthetaR hrsmall
  have hdist := actual_shear_seed_distance hq hU hSU hY hrange hstart hode
    (mul_pos hL hr) hT hp.2 htime hclose
  have htimeAbs : |p 0| ≤ L*r := abs_le.mpr htime
  have hdist' : |Y (p 1) (p 0)+q0*p 0-p 1| ≤ r/10 := by
    have he : (1/(10*L))*(L*r) = r/10 := by
      field_simp [hL.ne']
    exact hdist.trans ((mul_le_mul_of_nonneg_left htimeAbs (by positivity)).trans_eq he)
  have hsabs : |p 1| ≤ |Y (p 1) (p 0)+q0*p 0-p 1|+|Y (p 1) (p 0)+q0*p 0| := by
    calc
      |p 1| = |(Y (p 1) (p 0)+q0*p 0)-(Y (p 1) (p 0)+q0*p 0-p 1)| := by congr 1; ring
      _ ≤ |Y (p 1) (p 0)+q0*p 0|+|Y (p 1) (p 0)+q0*p 0-p 1| := abs_sub _ _
      _ = _ := add_comm _ _
  linarith

theorem pulseTensor_not_tsupport_exterior_seed
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {M q0 L r a delta tau : ℝ} (hM : 0 ≤ M) (hL : 0 < L) (hr : 0 < r)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    (hq0 : |q0| ≤ 1/20) (hcenter : |q 0-q0| ≤ 1/(100*L))
    (hT : L*r < 2) (ha : 0 < a) (haL : a ≤ L*r)
    (hrsmall : M*(r+107*(L*r)/100) ≤ 9/(100*L))
    (hd : 0 < delta) (ht : 0 < tau) (hwidth : delta/(2*tau) ≤ r/4)
    (N : ℕ) {p : Coord} (hp : p ∈ capChartDomain) (hseed : r/2 ≤ |p 1|) :
    capChart Y p ∉ tsupport (pulseTensor q0 a N delta tau) := by
  intro hin
  have hbox := pulseTensor_tsupport_subset ha hd ht N hin
  exact (not_lt_of_ge hseed) (pulseBox_seed_abs_lt_half hq hU hSU hY hrange hstart hode
    hsmall hM hL hr hpartial hq0 hcenter hT haL hrsmall hwidth hp hbox)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSegmentDomain
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def qHeightJetSegment (z0 z : Coord → ℝ) (sigma : ℝ) (p : Coord) : DarbouxState :=
  stateSegment (qSolutionJet z0 p) (qSolutionJet z p) sigma

@[simp] theorem stateSegment_zero (w0 w1 : DarbouxState) : stateSegment w0 w1 0 = w0 := by
  simp [stateSegment]

@[simp] theorem stateSegment_one (w0 w1 : DarbouxState) : stateSegment w0 w1 1 = w1 := by
  simp [stateSegment]

theorem stateSegment_hasDerivAt (w0 w1 : DarbouxState) (sigma : ℝ) :
    HasDerivAt (stateSegment w0 w1) (w1 - w0) sigma := by
  have he : (AffineMap.lineMap w0 w1 : ℝ → DarbouxState) = stateSegment w0 w1 := by
    funext t
    ext i
    simp [AffineMap.lineMap_apply_module, stateSegment]
  rw [← he]
  exact AffineMap.hasDerivAt_lineMap

theorem stateSegment_continuous (w0 w1 : DarbouxState) : Continuous (stateSegment w0 w1) :=
  continuous_iff_continuousAt.mpr (fun sigma => (stateSegment_hasDerivAt w0 w1 sigma).continuousAt)

theorem statePoint_qHeightJetSegment (z0 z : Coord → ℝ) (sigma : ℝ) (p : Coord) :
    statePoint (qHeightJetSegment z0 z sigma p) = p := by
  rw [qHeightJetSegment, statePoint_segment (by simp only [statePoint_qSolutionJet]),
    statePoint_qSolutionJet]

theorem state_distance_le_of_coordinate_error {w0 w1 : DarbouxState} {epsilon : ℝ}
    (heps : 0 ≤ epsilon) (hjet : ∀ i : Fin 6, |w1 i - w0 i| ≤ epsilon) :
    ‖w1 - w0‖ ≤ epsilon := by
  apply (pi_norm_le_iff_of_nonneg heps).mpr
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hjet i

theorem qSolutionJet_coordinate_error (z0 z : Coord → ℝ) (p : Coord) {epsilon : ℝ}
    (heps : 0 ≤ epsilon)
    (hgrad : ∀ i : Fin 2, |coordPartial i z p - coordPartial i z0 p| ≤ epsilon)
    (hmixed : |coordPartial 0 (coordPartial 1 z) p -
      coordPartial 0 (coordPartial 1 z0) p| ≤ epsilon)
    (hxx : |coordPartial 0 (coordPartial 0 z) p -
      coordPartial 0 (coordPartial 0 z0) p| ≤ epsilon) :
    ∀ i : Fin 6, |qSolutionJet z p i - qSolutionJet z0 p i| ≤ epsilon := by
  intro i
  fin_cases i
  · simpa [qSolutionJet] using heps
  · simpa [qSolutionJet] using heps
  · exact hgrad 0
  · exact hgrad 1
  · exact hmixed
  · exact hxx

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_ActualLowerCutImage
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
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation

theorem actual_flow_preimage_near_center
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa : ℝ}
    {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hf : CapInductionFlow g U G Z d c e0 kappa z Y W)
    {t y : ℝ} (ht : |t| ≤ 1) (hy : |y| ≤ 3/4) :
    ∃ s ∈ Ioo (-1 : ℝ) 1, Y s t = y := by
  have ht2 : t ∈ Ioo (-2 : ℝ) 2 := by
    constructor <;> linarith [(abs_le.mp ht).1,(abs_le.mp ht).2]
  have hnegp : boxPoint t (-1) ∈ capChartDomain := by
    simpa [capChartDomain,coordinateRectangle,boxPoint] using And.intro ht2 (show (-1 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
  have hposp : boxPoint t 1 ∈ capChartDomain := by
    simpa [capChartDomain,coordinateRectangle,boxPoint] using And.intro ht2 (show (1 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
  have hneg : |Y (-1) t+1| ≤ (1 : ℝ)/50 := by
    simpa [capFlowHeight,boxPoint] using hf.displacement (boxPoint t (-1)) hnegp
  have hpos : |Y 1 t-1| ≤ (1 : ℝ)/50 := by
    simpa [capFlowHeight,boxPoint] using hf.displacement (boxPoint t 1) hposp
  have hlo : Y (-1) t < y := by linarith [(abs_le.mp hneg).2,(abs_le.mp hy).1]
  have hhi : y < Y 1 t := by linarith [(abs_le.mp hpos).1,(abs_le.mp hy).2]
  have hmap : MapsTo (fun s : ℝ => (s,t)) (Icc (-1 : ℝ) 1)
      (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) := by
    intro s hs
    exact ⟨⟨by linarith [hs.1],by linarith [hs.2]⟩,⟨ht2.1.le,ht2.2.le⟩⟩
  have hcont : ContinuousOn (fun s : ℝ => Y s t) (Icc (-1 : ℝ) 1) :=
    hf.continuous.comp (by fun_prop : ContinuousOn (fun s : ℝ => (s,t)) (Icc (-1 : ℝ) 1)) hmap
  obtain ⟨s,hs,hse⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) hcont ⟨hlo.le,hhi.le⟩
  refine ⟨s,⟨?_,?_⟩,hse⟩
  · by_contra hn
    have he : s = -1 := le_antisymm (le_of_not_gt hn) hs.1
    subst s
    linarith
  · by_contra hn
    have he : s = 1 := le_antisymm hs.2 (le_of_not_gt hn)
    subst s
    linarith

def lowerCutRectangle (L r : ℝ) (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) : LowerCapRectangle (-r/2) where
  left := -(2*L*r)
  right := 2*L*r
  bottom := -(3*r/2)
  top := -(3*r/4)
  left_gt := by nlinarith
  right_lt := by nlinarith
  bottom_gt := by linarith
  horizontal := by nlinarith [mul_pos hL hr]
  vertical := by linarith
  top_lt := by linarith
  ceiling_le := by linarith

theorem actual_lower_cut_in_cap_image
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa q0 L r : ℝ}
    {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hh : CapInductionHeight g U Z c e0 z) (hf : CapInductionFlow g U G Z d c e0 kappa z Y W)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2) (hLr : L*r ≤ 1/20)
    (hq0 : |q0| ≤ 1/20) (hcenter : |hessianQuotient g z 0-q0| ≤ 1/(100*L))
    (hrsmall : heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L))
    {t : ℝ} (ht : |t| ≤ L*r) :
    inverseShearCoordinates q0 (boxPoint t (-r)) ∈ (lowerCutRectangle L r hL hr hrhalf hLr).image Y := by
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  have hpartial (p : Coord) (hp : p ∈ modelSquare) (i : Fin 2) :
      |coordPartial i (hessianQuotient g z) p| ≤ M := hf.quotientBound [i] (by norm_num) p hp
  have hTpos : 0 < L*r := mul_pos hL hr
  have ht1 : |t| ≤ 1 := ht.trans (by linarith)
  have hqt : |q0*t| ≤ (1/20)*(L*r) := by
    rw [abs_mul]
    exact mul_le_mul hq0 ht (abs_nonneg _) (by norm_num)
  have hy : |-r-q0*t| ≤ 3/4 := by
    have h := abs_sub (-r) (q0*t)
    rw [abs_neg,abs_of_pos hr] at h
    linarith
  obtain ⟨s,hs,hse⟩ := actual_flow_preimage_near_center hf ht1 hy
  have hs2 : s ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have htt : t ∈ Icc (-(L*r)) (L*r) := abs_le.mp ht
  have htheta : |Y s t+q0*t| ≤ r := by
    rw [hse]
    have he : -r-q0*t+q0*t = -r := by ring
    rw [he,abs_neg,abs_of_pos hr]
  have hclose := flow_segment_quotient_near_center hf.quotientSmooth hf.domainOpen hf.squareSubset
    hf.continuous hf.range hf.start hf.ode hh.quotient hM hL hpartial hq0 hcenter
    hTpos (by linarith : L*r < 2) hs2 htt htheta hrsmall
  have hdist := actual_shear_seed_distance hf.quotientSmooth hf.domainOpen hf.squareSubset
    hf.continuous hf.range hf.start hf.ode hTpos (by linarith : L*r < 2) hs2 htt hclose
  have hdist' : |-r-s| ≤ r/10 := by
    have he : (1/(10*L))*(L*r) = r/10 := by
      rw [div_mul_eq_mul_div₀, one_mul, mul_comm (10 : ℝ) L, mul_div_mul_left _ _ hL.ne']
    have hbound := hdist.trans ((mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq he)
    simpa only [hse,sub_add_cancel] using hbound
  refine ⟨boxPoint t s,?_,?_⟩
  · change (boxPoint t s) ∈ closedRectangle (-(2*L*r)) (2*L*r) (-(3*r/2)) (-(3*r/4))
    constructor
    · simpa [boxPoint] using (show t ∈ Icc (-(2*L*r)) (2*L*r) by
        constructor <;> nlinarith [(abs_le.mp ht).1,(abs_le.mp ht).2])
    · simpa [boxPoint] using (show s ∈ Icc (-(3*r/2)) (-(3*r/4)) by
        constructor <;> linarith [(abs_le.mp hdist').1,(abs_le.mp hdist').2])
  · ext i
    fin_cases i <;> simp [capChart,capFlowHeight,coordinatePoint,boxPoint,inverseShearCoordinates,hse]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSpatialJets
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

def qSolutionJetCurve (z : Coord → ℝ) (y : ℝ) : ℝ → DarbouxState :=
  fun x => qSolutionJet z (coordinatePoint x y)

theorem qSolutionJet_contDiffOn {z : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (qSolutionJet z) U := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_apply ℝ ℝ 0 U
  · exact contDiffOn_apply ℝ ℝ 1 U
  · exact partial_contDiffOn hz hU 0
  · exact partial_contDiffOn hz hU 1
  · exact partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0
  · exact partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0

theorem qSolutionJetCurve_contDiffAt {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : coordinatePoint x y ∈ U) :
    ContDiffAt ℝ ∞ (qSolutionJetCurve z y) x :=
  ((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).comp x
    (horizontalPoint_contDiff y).contDiffAt

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QHighEquation
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

def heightQCoefficient (g : MetricField) (z : Coord → ℝ) (i : Fin 6) (p : Coord) : ℝ :=
  qFirstCoefficient g i (qSolutionJet z p)

def qDirectLinearization (g : MetricField) (z u : Coord → ℝ) (p : Coord) : ℝ :=
  heightQCoefficient g z 2 p * coordPartial 0 u p +
    heightQCoefficient g z 3 p * coordPartial 1 u p +
    heightQCoefficient g z 4 p * coordPartial 0 (coordPartial 1 u) p +
    heightQCoefficient g z 5 p * coordPartial 0 (coordPartial 0 u) p

def qSecondJetCorrection (g : MetricField) (z u : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 (heightQCoefficient g z 4) p * coordPartial 1 u p +
    coordPartial 0 (heightQCoefficient g z 5) p * coordPartial 0 u p

def qFirstJetPairRemainder (g : MetricField) (z : Coord → ℝ) (n : ℕ) (p : Coord) : ℝ :=
  coordPartial 0 (heightQCoefficient g z 2) p * coordPartial 0 (horizontalJet z n) p +
    coordPartial 0 (heightQCoefficient g z 3) p * coordPartial 1 (horizontalJet z n) p

def qCoordinateChainTerm (g : MetricField) (z : Coord → ℝ) (w : ChainWord) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ w.arity (sixVariableQ g) (qSolutionJet z p)
    (fun i => horizontalJet (qSolutionJet z) (w.order i) p)

def qCoordinateChainSum (g : MetricField) (z : Coord → ℝ) (ws : List ChainWord) (p : Coord) : ℝ :=
  (ws.map (fun w => qCoordinateChainTerm g z w p)).sum

def actualQHighRemainder (g : MetricField) (z : Coord → ℝ) (m : ℕ) (p : Coord) : ℝ :=
  qCoordinateChainSum g z (topResidualWords m) p +
    (m + 3 : ℝ) * qFirstJetPairRemainder g z (m + 2) p

theorem second_fderiv_comp_constant_direction_xi
    {F : DarbouxState → ℝ} {J : Coord → DarbouxState} {p : Coord}
    (hF : ContDiffAt ℝ ∞ F (J p)) (hJ : DifferentiableAt ℝ J p) (v : DarbouxState) :
    iteratedFDeriv ℝ 2 F (J p) ![coordPartial 0 J p, v] =
      coordPartial 0 (fun r => fderiv ℝ F (J r) v) p := by
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) (J p) :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun r => fderiv ℝ F (J r)) p := hdF.comp p hJ
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold coordPartial
  have hcomp : fderiv ℝ (fun r => fderiv ℝ F (J r)) p =
      (fderiv ℝ (fderiv ℝ F) (J p)).comp (fderiv ℝ J p) :=
    fderiv_comp p hdF hJ
  rw [fderiv_clm_apply hc (differentiableAt_const (c := v)), hcomp]
  simp

def qHighBTheta (g : MetricField) (z : Coord → ℝ) (ell : ℕ) (p : Coord) : ℝ :=
  heightQCoefficient g z 3 p + (ell : ℝ) * coordPartial 0 (heightQCoefficient g z 4) p

def qHighBXi (g : MetricField) (z : Coord → ℝ) (ell : ℕ) (p : Coord) : ℝ :=
  heightQCoefficient g z 2 p + (ell : ℝ) * coordPartial 0 (heightQCoefficient g z 5) p

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QResidualFactors
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

def qCoordinateChainCoefficient (g : MetricField) (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ w.arity (sixVariableQ g) (qSolutionJet z p)
    (fun i => Pi.single (r i) (1 : ℝ))

def qCoordinateChainFactor (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (i : Fin w.arity) (p : Coord) : ℝ :=
  horizontalJet (qSolutionJet z) (w.order i) p (r i)

def qChainFactorOrder (w : ChainWord) (r : Fin w.arity → Fin 6) (i : Fin w.arity) : ℕ :=
  w.order i + qFirstJetOffset (r i)

theorem qFirstJetOffset_le_one (i : Fin 6) : qFirstJetOffset i ≤ 1 := by
  fin_cases i <;> (first | (simp [qFirstJetOffset]; all_goals first | (norm_num [qFirstJetOffset]; done) | rfl | decide) | (norm_num [qFirstJetOffset]; done) | norm_num [qFirstJetOffset])

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

def qWordSliceBudget (C lengthFloor left right : ℝ) (H : ℝ≥0) (w : ChainWord) : ℝ≥0∞ :=
  ∑ _r : Fin w.arity → Fin 6,
    ‖C‖ₑ * spatialProductL2Budget lengthFloor left right H w.arity

def qChainSliceBudget (C lengthFloor left right : ℝ) (H : ℝ≥0)
    (ws : List ChainWord) : ℝ≥0∞ :=
  (ws.map (qWordSliceBudget C lengthFloor left right H)).sum

def qRemainderSliceBudget (C Cfirst lengthFloor left right : ℝ) (H : ℝ≥0)
    (m : ℕ) : ℝ≥0∞ :=
  qChainSliceBudget C lengthFloor left right H (topResidualWords m) +
    ‖(m + 3 : ℝ)‖ₑ * qPairSliceBudget Cfirst H

theorem qWordSliceBudget_lt_top (C lengthFloor left right : ℝ) (H : ℝ≥0) (w : ChainWord) :
    qWordSliceBudget C lengthFloor left right H w < (⊤ : ℝ≥0∞) := by
  unfold qWordSliceBudget
  exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.mul_lt_top (by finiteness)
    (spatialProductL2Budget_lt_top lengthFloor left right H w.arity))

theorem qChainSliceBudget_lt_top (C lengthFloor left right : ℝ) (H : ℝ≥0)
    (ws : List ChainWord) : qChainSliceBudget C lengthFloor left right H ws < (⊤ : ℝ≥0∞) := by
  induction ws with
  | nil => simp [qChainSliceBudget]
  | cons w ws ih =>
      exact ENNReal.add_lt_top.mpr ⟨qWordSliceBudget_lt_top C lengthFloor left right H w, ih⟩

theorem qRemainderSliceBudget_lt_top (C Cfirst lengthFloor left right : ℝ)
    (H : ℝ≥0) (m : ℕ) : qRemainderSliceBudget C Cfirst lengthFloor left right H m < (⊤ : ℝ≥0∞) := by
  unfold qRemainderSliceBudget qPairSliceBudget
  exact ENNReal.add_lt_top.mpr
    ⟨qChainSliceBudget_lt_top C lengthFloor left right H (topResidualWords m), by finiteness⟩

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

theorem coordinatePoint_continuous_slice (theta : ℝ) :
    Continuous (fun x : ℝ => coordinatePoint x theta) := by
  unfold coordinatePoint
  fun_prop

theorem aesm_slice {h : Coord → ℝ} {U : Set Coord} {theta left right : ℝ}
    (hh : ContinuousOn h U) (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U) :
    AEStronglyMeasurable (fun x => h (coordinatePoint x theta)) (volume.restrict (Icc left right)) :=
  (hh.comp (coordinatePoint_continuous_slice theta).continuousOn hseg).aestronglyMeasurable measurableSet_Icc

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QResidualActive
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

def QActiveComponents (w : ChainWord) (r : Fin w.arity → Fin 6) : Prop :=
  ∀ i, r i ≠ 1 ∧ (r i = 0 → w.order i = 1)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSpatialRestriction
attribute [-simp] _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero
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

def qSpatialLinear : QSpatialState →ₗ[ℝ] DarbouxState where
  toFun v := ![v 0, 0, v 1, v 2, v 3, v 4]
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp

def qSpatialCLM : QSpatialState →L[ℝ] DarbouxState :=
  LinearMap.toContinuousLinearMap qSpatialLinear

def qFixedTimeState (theta : ℝ) (v : QSpatialState) : DarbouxState :=
  qSpatialCLM v + Pi.single 1 theta

def qSpatialProjection (w : DarbouxState) : QSpatialState := ![w 0, w 2, w 3, w 4, w 5]

def qFixedTimeQ (g : MetricField) (theta : ℝ) : QSpatialState → ℝ :=
  sixVariableQ g ∘ qFixedTimeState theta

def qFixedTimeDomain (g : MetricField) (U : Set Coord) (theta : ℝ) : Set QSpatialState :=
  qFixedTimeState theta ⁻¹' darbouxQStateDomain g U

theorem qSpatialCLM_single (i : Fin 5) :
    qSpatialCLM (Pi.single i 1) = Pi.single (qSpatialAxis i) 1 := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [qSpatialCLM, qSpatialLinear, qSpatialAxis]

theorem qFixedTimeState_projection (w : DarbouxState) :
    qFixedTimeState (w 1) (qSpatialProjection w) = w := by
  ext i
  fin_cases i <;> simp [qFixedTimeState, qSpatialProjection, qSpatialCLM,
    qSpatialLinear]

theorem qFixedTimeState_contDiff (theta : ℝ) : ContDiff ℝ ∞ (qFixedTimeState theta) :=
  qSpatialCLM.contDiff.add contDiff_const

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricQSpatialBundle
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

def HorizontalMetricTwoJetBound (g : MetricField) (p : Coord) (N : ℕ) (G : ℝ) : Prop :=
  (∀ i j n, n ≤ N → |horizontalJet (fun x => g x i j) n p| ≤ G) ∧
  (∀ d i j n, n ≤ N → |horizontalJet (coordPartial d (fun x => g x i j)) n p| ≤ G) ∧
  (∀ d e i j n, n ≤ N →
    |horizontalJet (coordPartial d (coordPartial e (fun x => g x i j))) n p| ≤ G)

def qFixedTimeBaseDomain (U : Set Coord) (theta : ℝ) : Set QSpatialState :=
  {v | coordinatePoint (v 0) theta ∈ U}

theorem statePoint_qFixedTimeState (theta : ℝ) (v : QSpatialState) :
    statePoint (qFixedTimeState theta v) = coordinatePoint (v 0) theta := by
  ext i
  fin_cases i <;> simp [statePoint, qFixedTimeState, qSpatialCLM, qSpatialLinear,
    coordinatePoint]

theorem qFixedTimeBaseDomain_isOpen {U : Set Coord} (hU : IsOpen U) (theta : ℝ) :
    IsOpen (qFixedTimeBaseDomain U theta) :=
  hU.preimage (by unfold coordinatePoint; fun_prop)

theorem qSpatialCLM_norm_le : ‖qSpatialCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  fin_cases i
  · exact norm_le_pi_norm v 0
  · simp [qSpatialCLM, qSpatialLinear]
  · exact norm_le_pi_norm v 1
  · exact norm_le_pi_norm v 2
  · exact norm_le_pi_norm v 3
  · exact norm_le_pi_norm v 4

theorem qFixedTimeState_positive_jet_bound (theta : ℝ) (v : QSpatialState)
    {n : ℕ} (hn : 1 ≤ n) : ‖iteratedFDeriv ℝ n (qFixedTimeState theta) v‖ ≤ 1 := by
  cases n with
  | zero => omega
  | succ n =>
      rw [← norm_iteratedFDeriv_fderiv]
      have he : fderiv ℝ (qFixedTimeState theta) = (fun _ : QSpatialState => qSpatialCLM) := by
        funext w
        exact (qSpatialCLM.hasFDerivAt.add_const (Pi.single 1 theta)).fderiv
      rw [he]
      cases n with
      | zero => simpa only [norm_iteratedFDeriv_zero] using qSpatialCLM_norm_le
      | succ _ => simp only [iteratedFDeriv_succ_const] <;> norm_num

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_LocalMetricQActive
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem qSolutionJet_norm_bound_of_coordinateBound
    {z : Coord → ℝ} {S : Set Coord} {R Z : ℝ} (hR : 0 ≤ R)
    (hzB : CoordinateBound z S 2 Z)
    (hcoords : ∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) {p : Coord} (hp : p ∈ S) :
    ‖qSolutionJet z p‖ ≤ max R Z := by
  apply (pi_norm_le_iff_of_nonneg (hR.trans (le_max_left _ _))).mpr
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact (hcoords p hp).1.trans (le_max_left _ _)
  · exact (hcoords p hp).2.trans (le_max_left _ _)
  · exact (hzB [0] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [1] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 0] (by norm_num) p hp).trans (le_max_right _ _)

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

theorem qSpatialProjection_norm_le (w : DarbouxState) : ‖qSpatialProjection w‖ ≤ ‖w‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
  intro i
  fin_cases i
  · exact norm_le_pi_norm w 0
  · exact norm_le_pi_norm w 2
  · exact norm_le_pi_norm w 3
  · exact norm_le_pi_norm w 4
  · exact norm_le_pi_norm w 5

theorem qSpatialCLM_projection_of_time_zero {w : DarbouxState} (hw : w 1 = 0) :
    qSpatialCLM (qSpatialProjection w) = w := by
  have he := qFixedTimeState_projection w
  simpa only [qFixedTimeState, hw, Pi.single_zero, add_zero] using he

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QEnergyApplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem spatialProductL2Budget_mono_width
    {lengthFloor left right width : ℝ} (H : ℝ≥0) (n : ℕ)
    (hwidth : right - left ≤ width) :
    spatialProductL2Budget lengthFloor left right H n ≤
      spatialProductL2Budget lengthFloor 0 width H n := by
  have hvol : volume (Icc left right) ≤ volume (Icc (0 : ℝ) width) := by
    rw [Real.volume_Icc, Real.volume_Icc, sub_zero]
    exact ENNReal.ofReal_le_ofReal hwidth
  exact mul_le_mul' le_rfl (add_le_add le_rfl
    (ENNReal.rpow_le_rpow hvol (by norm_num : 0 ≤ 1 / (2 : ℝ))))

theorem qRemainderSliceBudget_mono_width
    {C Cfirst lengthFloor left right width : ℝ} (H : ℝ≥0) (m : ℕ)
    (hwidth : right - left ≤ width) :
    qRemainderSliceBudget C Cfirst lengthFloor left right H m ≤
      qRemainderSliceBudget C Cfirst lengthFloor 0 width H m := by
  have hword (w : ChainWord) : qWordSliceBudget C lengthFloor left right H w ≤
      qWordSliceBudget C lengthFloor 0 width H w := by
    apply Finset.sum_le_sum
    intro _ _
    exact mul_le_mul' le_rfl (spatialProductL2Budget_mono_width H w.arity hwidth)
  have hsum (ws : List ChainWord) : qChainSliceBudget C lengthFloor left right H ws ≤
      qChainSliceBudget C lengthFloor 0 width H ws := by
    induction ws with
    | nil => exact le_rfl
    | cons w ws ih => exact add_le_add (hword w) ih
  exact add_le_add (hsum (topResidualWords m)) le_rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QFirstJetEnergy
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

theorem real_slice_eLpNorm_two_le_of_square_integral
    {f : ℝ → ℝ} {left right : ℝ} {B : ℝ≥0}
    (hlr : left ≤ right) (hf : MemLp f 2 (volume.restrict (Icc left right)))
    (hB : (∫ x in left..right, f x ^ 2) ≤ (B : ℝ)^2) :
    eLpNorm f 2 (volume.restrict (Icc left right)) ≤ (B : ℝ≥0∞) := by
  rw [intervalIntegral.integral_of_le hlr, restrict_Ioc_eq_restrict_Icc,
    integral_square_eq_L2_norm_square hf, Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp] at hB
  apply (ENNReal.toReal_le_toReal hf.eLpNorm_ne_top (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mp
  change (eLpNorm f 2 (volume.restrict (Icc left right))).toReal ≤ (B : ℝ)
  exact (sq_le_sq₀ ENNReal.toReal_nonneg B.2).mp hB

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_LocalQResidualL2
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

theorem HorizontalMetricTwoJetBound.mono_order
    {g : MetricField} {p : Coord} {N M : ℕ} {G : ℝ}
    (h : HorizontalMetricTwoJetBound g p N G) (hMN : M ≤ N) :
    HorizontalMetricTwoJetBound g p M G :=
  ⟨fun i j n hn => h.1 i j n (hn.trans hMN),
    fun d i j n hn => h.2.1 d i j n (hn.trans hMN),
    fun d e i j n hn => h.2.2 d e i j n (hn.trans hMN)⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricHorizontalRequests
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem horizontalJet_coordinate_word_prefix (f : Coord → ℝ) (ds : List (Fin 2)) (n : ℕ) :
    horizontalJet (iteratedCoordPartial ds f) n =
      iteratedCoordPartial (List.replicate n 0 ++ ds) f := by
  induction n with
  | zero => rfl
  | succ n hn =>
      simp only [horizontalJet, List.replicate_succ, List.cons_append, iteratedCoordPartial, hn]

theorem coordinateMetricBound_to_horizontalTwoJet
    {g : MetricField} {S : Set Coord} {N : ℕ} {G : ℝ}
    (hgB : ∀ i j, CoordinateBound (fun p => g p i j) S (N + 2) G)
    {p : Coord} (hp : p ∈ S) : HorizontalMetricTwoJetBound g p N G := by
  have hb (i j : Fin 2) (ds : List (Fin 2)) (hds : ds.length ≤ 2) (n : ℕ) (hn : n ≤ N) :
      |horizontalJet (iteratedCoordPartial ds (fun x => g x i j)) n p| ≤ G := by
    rw [horizontalJet_coordinate_word_prefix]
    apply hgB i j _ _ p hp
    simp only [List.length_append, List.length_replicate]
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro i j n hn
    exact hb i j [] (by simp) n hn
  · intro d i j n hn
    exact hb i j [d] (by simp) n hn
  · intro d e i j n hn
    exact hb i j [d, e] (by simp) n hn

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSpatialSlabData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def QLowBounds (g : MetricField) (z : Coord → ℝ) (S : Set Coord)
    (s0 M speed : ℝ) : Prop :=
  ∀ p ∈ S, s0 ≤ heightQCoefficient g z 5 p ∧
    |heightQCoefficient g z 2 p| ≤ M ∧ |heightQCoefficient g z 3 p| ≤ M ∧
    |heightQCoefficient g z 5 p| ≤ M ∧
    |coordPartial 0 (heightQCoefficient g z 4) p| ≤ M ∧
    |coordPartial 0 (heightQCoefficient g z 5) p| ≤ M ∧
    |coordPartial 1 (heightQCoefficient g z 5) p| ≤ M ∧
    |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed

theorem QLowBounds.high_coefficients
    {g : MetricField} {z : Coord → ℝ} {S : Set Coord} {s0 M speed : ℝ}
    (h : QLowBounds g z S s0 M speed) (hM : 0 ≤ M) (ell : ℕ) {p : Coord} (hp : p ∈ S) :
    |qHighBTheta g z ell p| ≤ M * (ell + 1) ∧
    |qHighBXi g z ell p| ≤ M * (ell + 1) ∧
    |coordPartial 0 (heightQCoefficient g z 4) p| ≤ M * (ell + 1) ∧
    |coordPartial 0 (heightQCoefficient g z 5) p| ≤ M * (ell + 1) ∧
    |coordPartial 1 (heightQCoefficient g z 5) p| ≤ M * (ell + 1) := by
  obtain ⟨_, h2, h3, _, h4x, h5x, h5t, _⟩ := h p hp
  have he : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hB : M ≤ M * (ell + 1) := by nlinarith
  have hbt : |qHighBTheta g z ell p| ≤ M * (ell + 1) := by
    unfold qHighBTheta
    calc
      _ ≤ |heightQCoefficient g z 3 p| + |(ell : ℝ) * coordPartial 0 (heightQCoefficient g z 4) p| := abs_add_le _ _
      _ ≤ M + (ell : ℝ) * M := by
        rw [abs_mul, abs_of_nonneg he]
        exact add_le_add h3 (mul_le_mul_of_nonneg_left h4x he)
      _ = _ := by ring
  have hbx : |qHighBXi g z ell p| ≤ M * (ell + 1) := by
    unfold qHighBXi
    calc
      _ ≤ |heightQCoefficient g z 2 p| + |(ell : ℝ) * coordPartial 0 (heightQCoefficient g z 5) p| := abs_add_le _ _
      _ ≤ M + (ell : ℝ) * M := by
        rw [abs_mul, abs_of_nonneg he]
        exact add_le_add h2 (mul_le_mul_of_nonneg_left h5x he)
      _ = _ := by ring
  exact ⟨hbt, hbx, h4x.trans hB, h5x.trans hB, h5t.trans hB⟩

theorem shrinkingSlab_mono_top {xl xr a b t speed : ℝ} (ht : t ≤ b) :
    shrinkingSlab xl xr a t speed ⊆ shrinkingSlab xl xr a b speed := by
  intro p hp
  exact ⟨⟨hp.1.1, hp.1.2.trans ht⟩, hp.2⟩

theorem SpatialSliceL2Bound.mono_order_budget
    {ι : Type*} {F : ι → Coord → ℝ} {theta left right : ℝ}
    {N n : ℕ} {H H' : ℝ≥0}
    (h : SpatialSliceL2Bound F theta left right N H) (hn : n ≤ N) (hH : H ≤ H') :
    SpatialSliceL2Bound F theta left right n H' := by
  intro i k hk
  exact (h i k (hk.trans hn)).trans (by exact_mod_cast hH)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QLowActualBounds
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem second_fderiv_comp_constant_coordinate
    {F : DarbouxState → ℝ} {J : Coord → DarbouxState} {p : Coord}
    (hF : ContDiffAt ℝ ∞ F (J p)) (hJ : DifferentiableAt ℝ J p)
    (j : Fin 2) (v : DarbouxState) :
    iteratedFDeriv ℝ 2 F (J p) ![coordPartial j J p, v] =
      coordPartial j (fun r => fderiv ℝ F (J r) v) p := by
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) (J p) :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun r => fderiv ℝ F (J r)) p := hdF.comp p hJ
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold coordPartial
  have hcomp : fderiv ℝ (fun r => fderiv ℝ F (J r)) p =
      (fderiv ℝ (fderiv ℝ F) (J p)).comp (fderiv ℝ J p) := by
    exact fderiv_comp p hdF hJ
  rw [fderiv_clm_apply hc (differentiableAt_const (c := v)), hcomp]
  simp

theorem heightQCoefficient_value_bound {g : MetricField} {z : Coord → ℝ}
    {p : Coord} {C : ℝ}
    (hQ : ‖iteratedFDeriv ℝ 1 (sixVariableQ g) (qSolutionJet z p)‖ ≤ C) (i : Fin 6) :
    |heightQCoefficient g z i p| ≤ C := by
  change ‖fderiv ℝ (sixVariableQ g) (qSolutionJet z p) (Pi.single i 1)‖ ≤ C
  have hb := (fderiv ℝ (sixVariableQ g) (qSolutionJet z p)).le_opNorm (Pi.single i 1)
  simp only [Pi.norm_single, norm_one, mul_one] at hb
  exact hb.trans (by simpa only [norm_iteratedFDeriv_one] using hQ)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QCoefficientTube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def qCompactTube (g : MetricField) (S : Set Coord) (M c : ℝ) : Set DarbouxState :=
  stateBaseCompact S M ∩ (fun w => |stateQDenominator g w|) ⁻¹' Ici c

theorem qCompactTube_subset_domain {g : MetricField} {U S : Set Coord}
    (hSU : S ⊆ U) (M : ℝ) {c : ℝ} (hc : 0 < c) :
    qCompactTube g S M c ⊆ darbouxQStateDomain g U := by
  intro w hw
  refine ⟨hSU hw.1.1, ?_⟩
  intro hz
  have hh : c ≤ |stateQDenominator g w| := hw.2
  rw [hz, abs_zero] at hh
  linarith

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSegmentAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def averagedQCoefficient (g : MetricField) (w0 w1 : DarbouxState) (i : Fin 6) : ℝ :=
  ∫ sigma in (0 : ℝ)..1, qFirstCoefficient g i (stateSegment w0 w1 sigma)

theorem sixVariableQ_fderiv_apply (g : MetricField) (w v : DarbouxState) :
    fderiv ℝ (sixVariableQ g) w v = ∑ i, qFirstCoefficient g i w * v i := by
  calc
    _ = fderiv ℝ (sixVariableQ g) w (∑ i, v i • Pi.single i 1) :=
      congrArg (fderiv ℝ (sixVariableQ g) w) (pi_eq_sum_univ' v)
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, qFirstCoefficient, mul_comm]

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QActualSegmentTransfer
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

theorem stateSegment_norm_le {w0 w1 : DarbouxState} {W sigma : ℝ}
    (h0 : ‖w0‖ ≤ W) (h1 : ‖w1‖ ≤ W) (hs : sigma ∈ Icc (0 : ℝ) 1) :
    ‖stateSegment w0 w1 sigma‖ ≤ W := by
  have hs0 : 0 ≤ 1 - sigma := sub_nonneg.mpr hs.2
  calc
    _ ≤ ‖(1 - sigma) • w0‖ + ‖sigma • w1‖ := norm_add_le _ _
    _ = (1 - sigma) * ‖w0‖ + sigma * ‖w1‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hs0, abs_of_nonneg hs.1]
    _ ≤ (1 - sigma) * W + sigma * W :=
      add_le_add (mul_le_mul_of_nonneg_left h0 hs0) (mul_le_mul_of_nonneg_left h1 hs.1)
    _ = W := by ring

theorem stateSegment_sub_right_norm_le {w0 w1 : DarbouxState} {sigma : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1) :
    ‖stateSegment w0 w1 sigma - w1‖ ≤ ‖w0 - w1‖ := by
  have he : stateSegment w0 w1 sigma - w1 = (1 - sigma) • (w0 - w1) := by
    ext i
    simp only [stateSegment, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [hs.1])

end SmoothLocal.HighEquation

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

def qResidual (g : MetricField) (P : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 1 (coordPartial 1 P) p - sixVariableQ g (qSolutionJet P p)

theorem initialPoint_contDiff (a : ℝ) :
    ContDiff ℝ ∞ (fun x => (![x, a] : Coord)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorCauchyData
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

def heightCauchyValue (z : Coord → ℝ) (a : ℝ) (x : ℝ) : ℝ := z ![x, a]

def heightCauchyVelocity (z : Coord → ℝ) (a : ℝ) (x : ℝ) : ℝ :=
  coordPartial 1 z ![x, a]

theorem heightCauchyVelocity_contDiffOn {z : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (a : ℝ)
    (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U) :
    ContDiffOn ℝ ∞ (heightCauchyVelocity z a) I :=
  (partial_contDiffOn hz hU 1).comp (initialPoint_contDiff a).contDiffOn hcut

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_QPointwiseCauchyJets
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem coordinatePoint_eq_vector (x t : ℝ) : coordinatePoint x t = (![x,t] : Coord) := by
  ext i
  fin_cases i <;> simp [coordinatePoint]

theorem halfWidth_mem_inward_interval {L r t x : ℝ} (hL : 0 < L) (hr : 0 < r)
    (ht : t ∈ Icc (-r) 0) (hx : |x| ≤ L*r/2) :
    x ∈ Icc (inwardLeft (-(L*r)) (-r) (L/4) t)
      (inwardRight (L*r) (-r) (L/4) t) := by
  have hLr : 0 < L*r := mul_pos hL hr
  have hprod := mul_nonpos_of_nonneg_of_nonpos hL.le ht.2
  obtain ⟨hxl,hxr⟩ := abs_le.mp hx
  unfold inwardLeft inwardRight
  constructor <;> nlinarith

end SmoothLocal.Taylor

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

def actualCurvatureFirstInput (g : MetricField) (p : Coord) : CurvatureFirstInput :=
  ((fun i j => g p i j),(fun d i j => metricFirstJet g p d i j))

end SmoothLocal.Pulse

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

theorem matrix_entry_abs_le_norm (G : MetricMatrix) (i j : Fin 2) : |G i j| ≤ ‖G‖ := by
  simpa only [Real.norm_eq_abs] using
    (Matrix.norm_entry_le_entrywise_sup_norm G (i := i) (j := j))

theorem det_sub_le_first_distance (G H : MetricMatrix) {B e : ℝ}
    (hB : 0 ≤ B) (he : 0 ≤ e) (hG : ‖G‖ ≤ B) (hD : ‖H-G‖ ≤ e) :
    |H.det-G.det| ≤ 4*B*e+2*e^2 := by
  let D := H-G
  have hg (i j : Fin 2) : |G i j| ≤ B := (matrix_entry_abs_le_norm G i j).trans hG
  have hd (i j : Fin 2) : |D i j| ≤ e := (matrix_entry_abs_le_norm D i j).trans hD
  have hgd (i j k l : Fin 2) : |G i j*D k l| ≤ B*e := by
    rw [abs_mul]
    exact mul_le_mul (hg i j) (hd k l) (abs_nonneg _) hB
  have hdg (i j k l : Fin 2) : |D i j*G k l| ≤ e*B := by
    rw [abs_mul]
    exact mul_le_mul (hd i j) (hg k l) (abs_nonneg _) he
  have hdd (i j k l : Fin 2) : |D i j*D k l| ≤ e^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul (hd i j) (hd k l) (abs_nonneg _) he
  have hsum (i j k l : Fin 2) :
      |G i j*D k l+D i j*G k l+D i j*D k l| ≤ B*e+e*B+e^2 :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add (hgd i j k l) (hdg i j k l)) (hdd i j k l))
  have hEq : H.det-G.det =
      (G 0 0*D 1 1+D 0 0*G 1 1+D 0 0*D 1 1)-
        (G 0 1*D 1 0+D 0 1*G 1 0+D 0 1*D 1 0) := by
    simp only [D,Matrix.det_fin_two,Matrix.sub_apply]
    ring
  rw [hEq]
  calc
    _ ≤ |G 0 0*D 1 1+D 0 0*G 1 1+D 0 0*D 1 1|+
        |G 0 1*D 1 0+D 0 1*G 1 0+D 0 1*D 1 0| := abs_sub _ _
    _ ≤ (B*e+e*B+e^2)+(B*e+e*B+e^2) := add_le_add (hsum 0 0 1 1) (hsum 0 1 1 0)
    _ = _ := by ring

theorem det_sub_le_small_first_distance (G H : MetricMatrix) {B e : ℝ}
    (hB : 0 ≤ B) (he : 0 ≤ e) (he1 : e ≤ 1) (hG : ‖G‖ ≤ B) (hD : ‖H-G‖ ≤ e) :
    |H.det-G.det| ≤ (4*B+2)*e := by
  apply (det_sub_le_first_distance G H hB he hG hD).trans
  have hee : e^2 ≤ e := by nlinarith [mul_le_mul_of_nonneg_left he1 he]
  nlinarith

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QFirstJetFunctions
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

abbrev QFirstInput := CurvatureFirstInput × DarbouxState

def qFirstDet (a : QFirstInput) : ℝ := (Matrix.of a.1.1).det
def qFirstConnection (a : QFirstInput) (i j : Fin 2) : ℝ :=
  ∑ k, christoffelJet (Matrix.of a.1.1) a.1.2 k i j * stateGradient a.2 k
def qFirstXX (a : QFirstInput) : ℝ := a.2 5-qFirstConnection a 0 0
def qFirstMixed (a : QFirstInput) : ℝ := a.2 4-qFirstConnection a 0 1
def qFirstEnergy (a : QFirstInput) : ℝ :=
  qFirstDet a-(a.1.1 1 1*(stateGradient a.2 0)^2-
    (a.1.1 0 1+a.1.1 1 0)*stateGradient a.2 0*stateGradient a.2 1+
      a.1.1 0 0*(stateGradient a.2 1)^2)
def qFirstDensityFactor (a : QFirstInput) : ℝ :=
  qFirstEnergy a/(qFirstDet a*qFirstXX a)
def qFirstLower (a : QFirstInput) : ℝ :=
  qFirstConnection a 1 1+(qFirstMixed a)^2/qFirstXX a

def qFirstBase : Set QFirstInput := {a | qFirstDet a ≠ 0}
def qFirstDomain : Set QFirstInput := {a | qFirstDet a ≠ 0 ∧ qFirstXX a ≠ 0}
def qFirstBaseTube (M d : ℝ) : Set QFirstInput :=
  Metric.closedBall 0 M ∩ qFirstDet ⁻¹' Ici d
def qFirstTube (M d c : ℝ) : Set QFirstInput :=
  qFirstBaseTube M d ∩ qFirstXX ⁻¹' {v : ℝ | c ≤ |v|}

theorem qFirstDet_contDiff : ContDiff ℝ ∞ qFirstDet := by
  unfold qFirstDet
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  fun_prop

theorem qFirstBase_isOpen : IsOpen qFirstBase :=
  isOpen_ne_fun qFirstDet_contDiff.continuous continuous_const

theorem qFirstBaseTube_isCompact (M d : ℝ) : IsCompact (qFirstBaseTube M d) :=
  (isCompact_closedBall (0 : QFirstInput) M).inter_right
    (isClosed_Ici.preimage qFirstDet_contDiff.continuous)

theorem qFirstBaseTube_subset_base (M : ℝ) {d : ℝ} (hd : 0 < d) :
    qFirstBaseTube M d ⊆ qFirstBase := by
  intro a ha
  exact ne_of_gt (hd.trans_le ha.2)

theorem qFirstTube_subset_domain (M : ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    qFirstTube M d c ⊆ qFirstDomain := by
  intro a ha
  refine ⟨qFirstBaseTube_subset_base M hd ha.1,?_⟩
  intro hz
  have hh : c ≤ |qFirstXX a| := ha.2
  rw [hz,abs_zero] at hh
  linarith

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

def pulseStrip (a delta tau : ℝ) : Set Coord :=
  closedRectangle (-a) a (-(delta/tau)) (delta/tau)
def pulsePairPoint (q : ℝ × ℝ) : Coord := boxPoint q.2 q.1
def pulseWeightedMoment (a delta tau : ℝ) (f : Coord → ℝ) : ℝ :=
  ∫ q in pulsePairRectangle a delta tau, f (pulsePairPoint q)*pulseTest a tau q.2
    ∂volume.prod volume

theorem pulsePairPoint_continuous : Continuous pulsePairPoint := by
  unfold pulsePairPoint boxPoint
  fun_prop

theorem pulsePairPoint_mem {a delta tau : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ pulsePairRectangle a delta tau) : pulsePairPoint q ∈ pulseStrip a delta tau :=
  boxPoint_mem hq.2 hq.1

theorem pulsePair_integrableOn {a delta tau : ℝ} {f : Coord → ℝ}
    (hf : ContinuousOn f (pulseStrip a delta tau)) :
    IntegrableOn (fun q => f (pulsePairPoint q)) (pulsePairRectangle a delta tau)
      (volume.prod volume) :=
  (hf.comp pulsePairPoint_continuous.continuousOn (fun _ hq => pulsePairPoint_mem hq)).integrableOn_compact
    (pulsePairRectangle_isCompact a delta tau)

theorem pulsePair_integral_eq_rectangleIntegral {a delta tau : ℝ} {f : Coord → ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hf : ContinuousOn f (pulseStrip a delta tau)) :
    (∫ q in pulsePairRectangle a delta tau, f (pulsePairPoint q) ∂volume.prod volume) =
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau) f := by
  have htime : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hspace : -a ≤ a := by linarith
  rw [show pulsePairRectangle a delta tau =
    Icc (-(delta/tau)) (delta/tau) ×ˢ Icc (-a) a from rfl,
    setIntegral_prod _ (pulsePair_integrableOn hf)]
  unfold rectangleIntegral
  rw [intervalIntegral.integral_of_le htime,←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro theta htheta
  dsimp only
  rw [intervalIntegral.integral_of_le hspace,←integral_Icc_eq_integral_Ioc]
  rfl

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

def affineFirstJetMap (R : MetricMatrix) (a : CurvatureFirstInput) : CurvatureFirstInput :=
  ((fun i j => ∑ u, ∑ v, R u i*R v j*a.1 u v),
    (fun k i j => ∑ u, ∑ v, ∑ w, R u i*R v j*R w k*a.2 w u v))

theorem affineFirstJetMap_sub (R : MetricMatrix) (a b : CurvatureFirstInput) :
    affineFirstJetMap R (a-b) = affineFirstJetMap R a-affineFirstJetMap R b := by
  apply Prod.ext
  · funext i j
    simp only [affineFirstJetMap,Prod.fst_sub,Pi.sub_apply,Fin.sum_univ_two]
    ring
  · funext k i j
    simp only [affineFirstJetMap,Prod.snd_sub,Pi.sub_apply,Fin.sum_univ_two]
    ring

theorem affineFirstJetMap_norm_le_eight (R : MetricMatrix)
    (hR : ∀ i j, |R i j| ≤ 1) (a : CurvatureFirstInput) {e : ℝ}
    (he : 0 ≤ e) (ha : ‖a‖ ≤ e) : ‖affineFirstJetMap R a‖ ≤ 8*e := by
  have hval (i j : Fin 2) : |a.1 i j| ≤ e := by
    simpa only [Real.norm_eq_abs] using
      (((norm_le_pi_norm (a.1 i) j).trans (norm_le_pi_norm a.1 i)).trans (norm_fst_le a)).trans ha
  have hder (k i j : Fin 2) : |a.2 k i j| ≤ e := by
    simpa only [Real.norm_eq_abs] using
      ((((norm_le_pi_norm (a.2 k i) j).trans (norm_le_pi_norm (a.2 k) i)).trans
        (norm_le_pi_norm a.2 k)).trans (norm_snd_le a)).trans ha
  have hR2 (i j u v : Fin 2) : |R u i*R v j| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hR u i) (hR v j) (abs_nonneg _) zero_le_one
  have hR3 (i j k u v w : Fin 2) : |R u i*R v j*R w k| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hR2 i j u v) (hR w k) (abs_nonneg _) zero_le_one
  have hv (i j u v : Fin 2) : |R u i*R v j*a.1 u v| ≤ e := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hR2 i j u v) (hval u v) (abs_nonneg _) zero_le_one
  have hd (k i j u v w : Fin 2) : |R u i*R v j*R w k*a.2 w u v| ≤ e := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hR3 i j k u v w) (hder w u v) (abs_nonneg _) zero_le_one
  have hvsum (i j : Fin 2) : |∑ u, ∑ v, R u i*R v j*a.1 u v| ≤ 4*e := by
    have hh := abs_sum_fin_two_le (fun u => abs_sum_fin_two_le (hv i j u))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hdsum (k i j : Fin 2) : |∑ u, ∑ v, ∑ w, R u i*R v j*R w k*a.2 w u v| ≤ 8*e := by
    have hh := abs_sum_fin_two_le (fun u => abs_sum_fin_two_le
      (fun v => abs_sum_fin_two_le (hd k i j u v)))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  change max ‖(affineFirstJetMap R a).1‖ ‖(affineFirstJetMap R a).2‖ ≤ 8*e
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro j
    change ‖∑ u, ∑ v, R u i*R v j*a.1 u v‖ ≤ _
    rw [Real.norm_eq_abs]
    exact (hvsum i j).trans (by nlinarith)
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro k
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro j
    change ‖∑ u, ∑ v, ∑ w, R u i*R v j*R w k*a.2 w u v‖ ≤ 8*e
    rw [Real.norm_eq_abs]
    exact hdsum k i j

theorem inverseShearMatrix_entry_le_one {q0 : ℝ} (hq : |q0| ≤ 1) (i j : Fin 2) :
    |inverseShearMatrix q0 i j| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp [inverseShearMatrix,hq]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualComparisonEquation
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

def comparisonCoefficient (g : MetricField) (P z : Coord → ℝ) (i : Fin 6) (p : Coord) : ℝ :=
  averagedQCoefficient g (qSolutionJet P p) (qSolutionJet z p) i

def comparisonDifference (P z : Coord → ℝ) (p : Coord) : ℝ := z p-P p

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonCoefficientSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def comparisonStateMap (P z : Coord → ℝ) (q : Coord × ℝ) : DarbouxState :=
  qHeightJetSegment P z q.2 q.1

def comparisonIntegrand (g : MetricField) (P z : Coord → ℝ) (i : Fin 6)
    (q : Coord × ℝ) : ℝ := qFirstCoefficient g i (comparisonStateMap P z q)

def comparisonParameterDomain (g : MetricField) (P z : Coord → ℝ) (U : Set Coord) :
    Set (Coord × ℝ) :=
  (U ×ˢ (univ : Set ℝ)) ∩ comparisonStateMap P z ⁻¹' darbouxQStateDomain g U

theorem comparisonStateMap_contDiffOn {P z : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (comparisonStateMap P z) (U ×ˢ (univ : Set ℝ)) := by
  have h0 : ContDiffOn ℝ ∞ (fun q : Coord × ℝ => qSolutionJet P q.1)
      (U ×ˢ (univ : Set ℝ)) := (qSolutionJet_contDiffOn hU hP).comp contDiff_fst.contDiffOn
    (fun _ hq => hq.1)
  have h1 : ContDiffOn ℝ ∞ (fun q : Coord × ℝ => qSolutionJet z q.1)
      (U ×ˢ (univ : Set ℝ)) := (qSolutionJet_contDiffOn hU hz).comp contDiff_fst.contDiffOn
    (fun _ hq => hq.1)
  exact ((contDiffOn_const.sub contDiff_snd.contDiffOn).smul h0).add
    (contDiff_snd.contDiffOn.smul h1)

theorem comparisonCoefficient_eq_parameterIntegral (g : MetricField) (P z : Coord → ℝ)
    (i : Fin 6) :
    comparisonCoefficient g P z i = compactParameterIntegral (comparisonIntegrand g P z i) := by
  funext p
  change (∫ sigma in (0 : ℝ)..1, _) = ∫ sigma in Icc (0 : ℝ) 1, _
  simp only [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricPatchOpen
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Model

def metricQuadraticValue (G : MetricMatrix) (v : Coord) : ℝ := v ⬝ᵥ (G *ᵥ v)

theorem metricQuadraticValue_continuousAt {T : Type*} [TopologicalSpace T]
    {G : T → MetricMatrix} {v : T → Coord} {t : T}
    (hG : ∀ i j, ContinuousAt (fun a => G a i j) t)
    (hv : ∀ i, ContinuousAt (fun a => v a i) t) :
    ContinuousAt (fun a => metricQuadraticValue (G a) (v a)) t := by
  simp only [metricQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fun_prop

theorem posDef_of_positive_on_sphere {G : MetricMatrix} (hG : G.IsHermitian)
    (hQ : ∀ v ∈ Metric.sphere (0 : Coord) 1, 0 < metricQuadraticValue G v) : G.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hG
  intro v hv
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let w : Coord := ‖v‖⁻¹ • v
  have hw : w ∈ Metric.sphere (0 : Coord) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right]
    simp [w, norm_smul, hn]
  have heq : metricQuadraticValue G w = (‖v‖⁻¹)^2 * metricQuadraticValue G v := by
    simp only [metricQuadraticValue, w, Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    ring
  have hmul : 0 < (‖v‖⁻¹)^2 * metricQuadraticValue G v := by
    rw [← heq]
    exact hQ w hw
  have hs : 0 < (‖v‖⁻¹)^2 := sq_pos_of_ne_zero (inv_ne_zero hn)
  have hvQ : 0 < metricQuadraticValue G v := (mul_pos_iff_of_pos_left hs).mp hmul
  simpa only [metricQuadraticValue, star_trivial] using hvQ

theorem centralBox_subset_modelSquare : centralBox ⊆ modelSquare := by
  intro p hp
  constructor <;> intro i <;> linarith [hp.1 i, hp.2 i]

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_FiniteApproximationJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.HighEquation

theorem metricApproximationAccuracy_le_one {tau : ℕ} (htau : 1 ≤ tau) :
    metricApproximationAccuracy tau ≤ 1 := by
  have htauR : (1 : ℝ) ≤ (tau : ℝ) := by exact_mod_cast htau
  simpa only [metricApproximationAccuracy,div_one] using
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1) (one_le_pow₀ htauR : 1 ≤ (tau : ℝ)^tau))

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_BoundedClassSlabSmallness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

def boundedClassQuotientBudget (G d : ℝ) (M : ℕ) : ℝ :=
  heightQuotientJetBound G (M : ℝ) d (1 / (M : ℝ))

theorem boundedClassQuotientBudget_nonneg {G d : ℝ} {M : ℕ}
    (hG : 0 ≤ G) (hd : 0 < d) (hM : 0 < M) : 0 ≤ boundedClassQuotientBudget G d M :=
  heightQuotientJetBound_nonneg hG (Nat.cast_nonneg M) hd
    (one_div_pos.mpr (Nat.cast_pos.mpr hM))

theorem inverseShear_coordinate_sum_le {q0 L r : ℝ} {p : Coord}
    (_hr : 0 ≤ r) (hx : |p 0| ≤ L * r) (hy : |p 1| ≤ r) :
    |inverseShearCoordinates q0 p 0| + |inverseShearCoordinates q0 p 1| ≤
      r * (1 + (1 + |q0|) * L) := by
  change |p 0| + |p 1 - q0 * p 0| ≤ _
  calc
    _ ≤ |p 0| + (|p 1| + |q0 * p 0|) := add_le_add le_rfl (abs_sub _ _)
    _ ≤ L * r + (r + |q0| * (L * r)) := by
      rw [abs_mul]
      exact add_le_add hx (add_le_add hy (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
    _ = _ := by ring

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_BoundedPatchSlabGeometry
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
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

theorem inverseShear_slab_mem_centralBox {L r q0 : ℝ} {p : Coord}
    (hL : 1 ≤ L) (hr : 0 ≤ r) (hLr : L * r ≤ 1 / 20) (hq0 : |q0| ≤ 1 / 20)
    (hx : |p 0| ≤ L * r) (hy : |p 1| ≤ r) :
    inverseShearCoordinates q0 p ∈ centralBox := by
  have hrL : r ≤ L * r := by nlinarith
  have hrsmall : r ≤ 1 / 20 := hrL.trans hLr
  have hxsmall : |p 0| ≤ 1 / 20 := hx.trans hLr
  have hprod : |q0 * p 0| ≤ (1 / 20 : ℝ) * (1 / 20) := by
    rw [abs_mul]
    exact mul_le_mul hq0 hxsmall (abs_nonneg _) (by norm_num)
  have hysmall : |p 1 - q0 * p 0| ≤ (1 / 20 : ℝ) + (1 / 20) * (1 / 20) :=
    (abs_sub _ _).trans (add_le_add (hy.trans hrsmall) hprod)
  change (fun _ => -(1 / 5 : ℝ)) ≤ inverseShearCoordinates q0 p ∧
    inverseShearCoordinates q0 p ≤ (fun _ => (1 / 5 : ℝ))
  constructor
  · intro i
    fin_cases i
    · change -(1 / 5 : ℝ) ≤ p 0
      linarith [(abs_le.mp hxsmall).1]
    · change -(1 / 5 : ℝ) ≤ p 1 - q0 * p 0
      linarith [(abs_le.mp hysmall).1]
  · intro i
    fin_cases i
    · change p 0 ≤ (1 / 5 : ℝ)
      linarith [(abs_le.mp hxsmall).2]
    · change p 1 - q0 * p 0 ≤ (1 / 5 : ℝ)
      linarith [(abs_le.mp hysmall).2]

theorem shrinking_class_slab_axis_bounds {kappa r b : ℝ} {M : ℕ} {p : Coord}
    (hr : 0 ≤ r) (hb : b ≤ 0)
    (hp : p ∈ shrinkingSlab (-(boundedClassWidth kappa M * r)) (boundedClassWidth kappa M * r)
      (-r) b (boundedClassWidth kappa M / 4)) :
    |p 0| ≤ boundedClassWidth kappa M * r ∧ |p 1| ≤ r := by
  have ht := hp.1
  have hx := hp.2
  have hspeed : 0 ≤ boundedClassWidth kappa M / 4 :=
    div_nonneg (boundedClassWidth_pos kappa M).le (by norm_num)
  have hmove : 0 ≤ (boundedClassWidth kappa M / 4) * (p 1 - (-r)) :=
    mul_nonneg hspeed (sub_nonneg.mpr ht.1)
  unfold inwardLeft inwardRight at hx
  exact ⟨abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩,
    abs_le.mpr ⟨ht.1, by linarith [ht.2]⟩⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QContainingRectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem closedRectangle_compact (l r a b : ℝ) : IsCompact (closedRectangle l r a b) := by
  have he : closedRectangle l r a b = Icc (![l,a] : Coord) ![r,b] := by
    ext p
    constructor
    · intro hp
      constructor
      · intro i
        fin_cases i
        · exact hp.1.1
        · exact hp.2.1
      · intro i
        fin_cases i
        · exact hp.1.2
        · exact hp.2.2
    · intro hp
      exact ⟨⟨hp.1 0,hp.2 0⟩,⟨hp.1 1,hp.2 1⟩⟩
  rw [he]
  exact isCompact_Icc

theorem exists_containing_coordinateRectangle {U : Set Coord} (hU : IsOpen U)
    {R a b : ℝ} (hR : 0 < R) (hab : a ≤ b)
    (hbox : closedRectangle (-R) R a b ⊆ U) :
    ∃ radius lo hi : ℝ, R < radius ∧ lo < a ∧ b < hi ∧
      coordinateRectangle radius lo hi ⊆ U := by
  obtain ⟨e,he,hthick⟩ := (closedRectangle_compact (-R) R a b).exists_thickening_subset_open hU hbox
  refine ⟨R+e,a-e,b+e,by linarith,by linarith,by linarith,?_⟩
  intro p hp
  obtain ⟨x,hx,hxe⟩ := real_near_closed_interval (show -R ≤ R by linarith) he
    (show p 0 ∈ Ioo (-R-e) (R+e) by
      exact ⟨by linarith [hp.1.1],hp.1.2⟩)
  obtain ⟨t,ht,hte⟩ := real_near_closed_interval hab he hp.2
  apply hthick
  rw [Metric.mem_thickening_iff]
  refine ⟨![x,t],⟨hx,ht⟩,?_⟩
  rw [dist_eq_norm]
  apply (pi_norm_lt_iff he).mpr
  intro i
  fin_cases i
  · change ‖p 0-x‖ < e
    simpa only [Real.norm_eq_abs] using hxe
  · change ‖p 1-t‖ < e
    simpa only [Real.norm_eq_abs] using hte

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_ActualPatchQRectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic

theorem centralBox_subset_modelOpenSquare : centralBox ⊆ modelOpenSquare := by
  intro p hp
  change p 0 ∈ Ioo (-3 : ℝ) 3 ∧ p 1 ∈ Ioo (-3 : ℝ) 3
  exact ⟨⟨by linarith [hp.1 0],by linarith [hp.2 0]⟩,
    ⟨by linarith [hp.1 1],by linarith [hp.2 1]⟩⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_PatchAddressModel
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation SmoothLocal.Model

def patchAddressModelDomain : Set Coord := Metric.ball 0 (13/4)

theorem patchAddressModelDomain_isOpen : IsOpen patchAddressModelDomain := Metric.isOpen_ball

theorem modelSquare_subset_patchAddressModelDomain : modelSquare ⊆ patchAddressModelDomain := by
  intro p hp
  have hnorm : ‖p‖ ≤ 3 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using (abs_le.mpr ⟨hp.1 i,hp.2 i⟩)
  change dist p 0 < 13/4
  rw [dist_zero_right]
  linarith

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSameStripMargins
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem qSolutionJet_norm_bound_of_words {z : Coord → ℝ} {p : Coord} {R Z : ℝ}
    (hR : 0 ≤ R) (hpB : ‖p‖ ≤ R)
    (hjet : ∀ ds : List (Fin 2), ds.length ≤ 2 → |iteratedCoordPartial ds z p| ≤ Z) :
    ‖qSolutionJet z p‖ ≤ max R Z := by
  have hcoord (i : Fin 2) : |p i| ≤ R := (norm_le_pi_norm p i).trans hpB
  apply (pi_norm_le_iff_of_nonneg (hR.trans (le_max_left _ _))).mpr
  intro i
  fin_cases i
  · exact (hcoord 0).trans (le_max_left _ _)
  · exact (hcoord 1).trans (le_max_left _ _)
  · exact (hjet [0] (by norm_num)).trans (le_max_right _ _)
  · exact (hjet [1] (by norm_num)).trans (le_max_right _ _)
  · exact (hjet [0, 1] (by norm_num)).trans (le_max_right _ _)
  · exact (hjet [0, 0] (by norm_num)).trans (le_max_right _ _)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ShearedPulseRegions
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

def shearedModelSquare (q0 : ℝ) : Set Coord :=
  inverseShearCoordinates q0 ⁻¹' modelSquare

def sectionFourClosedSlab (L r : ℝ) : Set Coord :=
  {p | |p 0| ≤ L*r ∧ |p 1| ≤ r}

theorem sectionFourClosedSlab_mem_shearedModelSquare
    {q0 L r : ℝ} (_hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20)
    {p : Coord} (hp : p ∈ sectionFourClosedSlab L r) :
    p ∈ shearedModelSquare q0 := by
  have hx : |p 0| ≤ (1/20 : ℝ) := hp.1.trans hLr
  have hmul : |q0 * p 0| ≤ (1/20 : ℝ) * (1/20) := by
    rw [abs_mul]
    exact mul_le_mul hq0 hx (abs_nonneg _) (by norm_num)
  have hy : |p 1 - q0 * p 0| ≤ r + (1/20 : ℝ)*(1/20) :=
    (abs_sub _ _).trans (add_le_add hp.2 hmul)
  have hx3 : |p 0| ≤ 3 := hx.trans (by norm_num)
  have hy3 : |p 1 - q0*p 0| ≤ 3 := hy.trans (by linarith)
  constructor <;> intro i <;> fin_cases i
  · exact (abs_le.mp hx3).1
  · exact (abs_le.mp hy3).1
  · exact (abs_le.mp hx3).2
  · exact (abs_le.mp hy3).2

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseEdgeReferenceDistance
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

theorem metricApproximationAccuracy_le_inverse {tau : ℕ} (htau : 1 ≤ tau) :
    metricApproximationAccuracy tau ≤ 1 / (tau : ℝ) := by
  have htauR : (1 : ℝ) ≤ (tau : ℝ) := by exact_mod_cast htau
  have htauP : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le htauR
  unfold metricApproximationAccuracy
  exact one_div_le_one_div_of_le htauP (le_self_pow₀ htauR (Nat.ne_of_gt htau))

theorem exists_first_error_threshold {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ tau0 : ℕ, 1 ≤ tau0 ∧ ∀ tau : ℕ, tau0 ≤ tau →
      8 * metricApproximationAccuracy tau ≤ epsilon := by
  obtain ⟨n, hn⟩ := exists_nat_gt (8 / epsilon)
  refine ⟨max 1 n, le_max_left _ _, ?_⟩
  intro tau htau
  have htauN : 1 ≤ tau := (le_max_left _ _).trans htau
  have hnN : n ≤ tau := (le_max_right _ _).trans htau
  have htauR : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le (by exact_mod_cast htauN)
  have hnR : (n : ℝ) ≤ (tau : ℝ) := by exact_mod_cast hnN
  have hh : 8 < (n : ℝ) * epsilon := (div_lt_iff₀ he).mp hn
  have hb : 8 / (tau : ℝ) ≤ epsilon := (div_le_iff₀ htauR).mpr (by nlinarith)
  exact (mul_le_mul_of_nonneg_left (metricApproximationAccuracy_le_inverse htauN) (by norm_num)).trans
    (by simpa only [mul_one_div] using hb)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseTestEnergy
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Hyperbolic

theorem pulse_strip_pairing_bound (i : Fin 2) {a delta tau F S0 G : ℝ}
    {test : ℝ → ℝ} {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hF : 0 ≤ F) (hS0 : 0 ≤ S0) (_ : 0 ≤ G)
    (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U)
    (htest : Continuous test) (htestB : ∀ x, |test x| ≤ F)
    (hSB : ∀ p ∈ pulseStrip a delta tau, |S p| ≤ S0)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ G) :
    |∫ theta in Icc (-(delta/tau)) (delta/tau), ∫ x in Icc (-a) a,
      test x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)| ≤
      (F*S0*Real.sqrt (2*a)*G)*(2*delta/tau) := by
  have hslice (theta : ℝ) (htheta : theta ∈ Icc (-(delta/tau)) (delta/tau)) :
      |∫ x in Icc (-a) a, test x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)| ≤
        F*S0*Real.sqrt (2*a)*G := by
    have hmap : ∀ x ∈ Icc (-a) a, boxPoint x theta ∈ U :=
      fun x hx => hSU (boxPoint_mem hx htheta)
    have hSc : ContinuousOn (fun x => S (boxPoint x theta)) (Icc (-a) a) :=
      hS.continuousOn.comp (by unfold boxPoint; fun_prop) hmap
    have hvc : ContinuousOn (fun x => coordPartial i v (boxPoint x theta)) (Icc (-a) a) :=
      (partial_contDiffOn hv hU i).continuousOn.comp (by unfold boxPoint; fun_prop) hmap
    have hproduct : ∀ x ∈ Icc (-a) a, |test x*S (boxPoint x theta)| ≤ F*S0 := by
      intro x hx
      rw [abs_mul]
      exact mul_le_mul (htestB x) (hSB _ (boxPoint_mem hx htheta)) (abs_nonneg _) hF
    have hh := real_Icc_pairing_bound (by linarith : -a ≤ a) (mul_nonneg hF hS0)
      (htest.continuousOn.mul hSc) hvc hproduct (hL2 theta htheta)
    simpa only [Pi.mul_apply,sub_neg_eq_add,←two_mul] using hh
  have htime : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hmajor : Integrable (fun _ : ℝ => F*S0*Real.sqrt (2*a)*G)
      (volume.restrict (Icc (-(delta/tau)) (delta/tau))) :=
    (continuous_const : Continuous
      (fun _ : ℝ => F*S0*Real.sqrt (2*a)*G)).continuousOn.integrableOn_Icc
  have hpoint : ∀ᵐ theta ∂volume.restrict (Icc (-(delta/tau)) (delta/tau)),
      ‖∫ x in Icc (-a) a, test x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)‖ ≤
        F*S0*Real.sqrt (2*a)*G := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with theta htheta
    simpa only [Real.norm_eq_abs] using hslice theta htheta
  have hi := norm_integral_le_of_norm_le hmajor hpoint
  rw [setIntegral_const,Real.volume_real_Icc_of_le htime,smul_eq_mul] at hi
  simp only [Real.norm_eq_abs] at hi
  apply hi.trans_eq
  ring

theorem pulse_derivative_pairing_delta_sq (i : Fin 2) {a delta tau S0 M : ℝ} {N : ℕ}
    {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hS0 : 0 ≤ S0) (hM : 0 ≤ M) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U)
    (hSB : ∀ p ∈ pulseStrip a delta tau, |S p| ≤ S0)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ M*delta*tau/tau^N) :
    |∫ theta in Icc (-(delta/tau)) (delta/tau), ∫ x in Icc (-a) a,
      deriv (pulseTest a tau) x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)| ≤
      (2*pulseTestDerivativeBound a ha*S0*Real.sqrt (2*a)*M)*delta^2*tau/tau^N := by
  have htpos : 0 < tau := zero_lt_one.trans_le ht
  have hF : 0 ≤ pulseTestDerivativeBound a ha*tau :=
    mul_nonneg (pulseTestDerivativeBound_nonneg ha) htpos.le
  have hG : 0 ≤ M*delta*tau/tau^N := by positivity
  have htest : Continuous (deriv (pulseTest a tau)) :=
    (contDiff_infty_iff_deriv.mp (pulseTest_contDiff a tau)).2.continuous
  have hh := pulse_strip_pairing_bound i ha hd htpos hF hS0 hG hU hSU hS hv htest
    (pulseTest_deriv_bound ha ht) hSB hL2
  apply hh.trans_eq
  field_simp [htpos.ne']

theorem pulse_test_pairing_extra_inv_tau (i : Fin 2) {a delta tau S0 M : ℝ} {N : ℕ}
    {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hS0 : 0 ≤ S0) (hM : 0 ≤ M) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U)
    (hSB : ∀ p ∈ pulseStrip a delta tau, |S p| ≤ S0)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ M*delta*tau/tau^N) :
    |∫ theta in Icc (-(delta/tau)) (delta/tau), ∫ x in Icc (-a) a,
      pulseTest a tau x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)| ≤
      (2*axisBumpDerivativeBound a ha 0*S0*Real.sqrt (2*a)*M)*delta^2/tau^N := by
  have htpos : 0 < tau := zero_lt_one.trans_le ht
  have hF := (axisBumpDerivativeBound_pos ha 0).le
  have hG : 0 ≤ M*delta*tau/tau^N := by positivity
  have htest (x : ℝ) : |pulseTest a tau x| ≤ axisBumpDerivativeBound a ha 0 := by
    have hχ : |axisBump a x| ≤ axisBumpDerivativeBound a ha 0 := by
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using axisBump_derivative_le ha 0 x
    exact (pulseTest_abs_le a tau x).trans ((le_abs_self _).trans hχ)
  have hh := pulse_strip_pairing_bound i ha hd htpos hF hS0 hG hU hSU hS hv
    (pulseTest_continuous a tau) htest hSB hL2
  apply hh.trans_eq
  field_simp [htpos.ne']

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseSpatialParts
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem pulse_boxPoint_zero (x t : ℝ) : boxPoint x t 0 = x := by
  change x*1+t*0=x
  ring

theorem pulse_boxPoint_one (x t : ℝ) : boxPoint x t 1 = t := by
  change x*0+t*1=t
  ring

def pulseSpatialTest (a tau : ℝ) (p : Coord) : ℝ := pulseTest a tau (p 0)

theorem pulseSpatialTest_contDiff (a tau : ℝ) : ContDiff ℝ ∞ (pulseSpatialTest a tau) :=
  (pulseTest_contDiff a tau).comp (contDiff_apply ℝ ℝ 0)

theorem pulseSpatialTest_partial (a tau : ℝ) (p : Coord) :
    coordPartial 0 (pulseSpatialTest a tau) p = deriv (pulseTest a tau) (p 0) := by
  have hψ := ((pulseTest_contDiff a tau).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (p 0)).hasDerivAt
  have hproj : HasFDerivAt (fun q : Coord => q 0) (ContinuousLinearMap.proj 0) p :=
    (ContinuousLinearMap.proj 0 : Coord →L[ℝ] ℝ).hasFDerivAt
  have hh := hψ.comp_hasFDerivAt p hproj
  change fderiv ℝ ((pulseTest a tau) ∘ (fun q : Coord => q 0)) p (Pi.single 0 1) = _
  rw [hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.proj_apply,Pi.single_eq_same,smul_eq_mul,mul_one]

theorem rectangleIntegral_eq_Icc_slices (f : Coord → ℝ) {l r b t : ℝ}
    (hlr : l ≤ r) (hbt : b ≤ t) :
    rectangleIntegral l r b t f = ∫ theta in Icc b t, ∫ x in Icc l r, f (boxPoint x theta) := by
  unfold rectangleIntegral
  rw [intervalIntegral.integral_of_le hbt,←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro theta htheta
  dsimp only
  rw [intervalIntegral.integral_of_le hlr,←integral_Icc_eq_integral_Ioc]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseTemporalParts
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem pulseSpatialTest_partial_time (a tau : ℝ) (p : Coord) :
    coordPartial 1 (pulseSpatialTest a tau) p = 0 := by
  have hψ := ((pulseTest_contDiff a tau).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (p 0)).hasDerivAt
  have hproj : HasFDerivAt (fun q : Coord => q 0) (ContinuousLinearMap.proj 0) p :=
    (ContinuousLinearMap.proj 0 : Coord →L[ℝ] ℝ).hasFDerivAt
  have hh := hψ.comp_hasFDerivAt p hproj
  change fderiv ℝ ((pulseTest a tau) ∘ (fun q : Coord => q 0)) p (Pi.single 1 1) = 0
  rw [hh.fderiv]
  simp [smul_apply,ContinuousLinearMap.proj_apply]

theorem rectangleIntegral_partial_time_boundary {l r b t : ℝ}
    {f : Coord → ℝ} {U : Set Coord}
    (hlr : l ≤ r) (hbt : b ≤ t) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hbox : closedRectangle l r b t ⊆ U) :
    rectangleIntegral l r b t (coordPartial 1 f) =
      (∫ x in l..r, f (boxPoint x t)) - (∫ x in l..r, f (boxPoint x b)) := by
  rw [rectangleIntegral_swap hlr hbt ((partial_contDiffOn hf hU 1).continuousOn.mono hbox)]
  have hinner (x : ℝ) (hx : x ∈ Icc l r) :
      (∫ theta in b..t, coordPartial 1 f (boxPoint x theta)) =
        f (boxPoint x t)-f (boxPoint x b) := by
    have hcont : ContinuousOn (fun theta => coordPartial 1 f (boxPoint x theta)) (uIcc b t) := by
      rw [uIcc_of_le hbt]
      exact (partial_contDiffOn hf hU 1).continuousOn.comp
        (by unfold boxPoint; fun_prop) (fun theta htheta => hbox (boxPoint_mem hx htheta))
    have hderiv (theta : ℝ) (htheta : theta ∈ uIcc b t) :
        HasDerivAt (fun s => f (boxPoint x s)) (coordPartial 1 f (boxPoint x theta)) theta := by
      have hp : boxPoint x theta ∈ U := hbox (boxPoint_mem hx
        (by simpa only [uIcc_of_le hbt] using htheta))
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      exact hd.hasFDerivAt.comp_hasDerivAt theta (boxPoint_hasDerivAt_s x theta)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have htcont : ContinuousOn (fun x => f (boxPoint x t)) (uIcc l r) := by
    rw [uIcc_of_le hlr]
    exact hf.continuousOn.comp (by unfold boxPoint; fun_prop)
      (fun x hx => hbox (boxPoint_mem hx ⟨hbt,le_rfl⟩))
  have hbcont : ContinuousOn (fun x => f (boxPoint x b)) (uIcc l r) := by
    rw [uIcc_of_le hlr]
    exact hf.continuousOn.comp (by unfold boxPoint; fun_prop)
      (fun x hx => hbox (boxPoint_mem hx ⟨le_rfl,hbt⟩))
  calc
    _ = ∫ x in l..r, (f (boxPoint x t)-f (boxPoint x b)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact hinner x (by simpa only [uIcc_of_le hlr] using hx)
    _ = _ := intervalIntegral.integral_sub htcont.intervalIntegrable hbcont.intervalIntegrable

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

theorem pulse_boxPoint_eq (x t : ℝ) : boxPoint x t = (![x,t] : Coord) := by
  ext i
  fin_cases i
  · change boxPoint x t 0=x
    exact pulse_boxPoint_zero x t
  · change boxPoint x t 1=t
    exact pulse_boxPoint_one x t

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

def testedOperatorSource (R S b c v : Coord → ℝ) (p : Coord) : ℝ :=
  hyperbolicOperator R S v p-b p*coordPartial 1 v p-c p*coordPartial 0 v p

theorem testedOperatorSource_contDiffOn {R S b c v : Coord → ℝ} {U : Set Coord}
    (hR : ContDiffOn ℝ ∞ R U) (hS : ContDiffOn ℝ ∞ S U)
    (hb : ContDiffOn ℝ ∞ b U) (hc : ContDiffOn ℝ ∞ c U)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (testedOperatorSource R S b c v) U :=
  ((((partial_contDiffOn (partial_contDiffOn hv hU 1) hU 1).sub
    (hR.mul (partial_contDiffOn (partial_contDiffOn hv hU 1) hU 0))).sub
    (hS.mul (partial_contDiffOn (partial_contDiffOn hv hU 0) hU 0))).sub
    (hb.mul (partial_contDiffOn hv hU 1))).sub (hc.mul (partial_contDiffOn hv hU 0))

theorem pulseWeightedMoment_eq_tested_rectangle {a delta tau : ℝ} {f : Coord → ℝ}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hf : ContinuousOn f (pulseStrip a delta tau)) :
    pulseWeightedMoment a delta tau f =
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau) (fun p => pulseSpatialTest a tau p*f p) := by
  have hh := pulsePair_integral_eq_rectangleIntegral ha.le hd ht
    ((pulseSpatialTest_contDiff a tau).continuous.continuousOn.mul hf)
  simp only [Pi.mul_def] at hh
  have he : (fun q : ℝ × ℝ => pulseSpatialTest a tau (pulsePairPoint q)*f (pulsePairPoint q)) =
      (fun q => f (pulsePairPoint q)*pulseTest a tau q.2) := by
    funext q
    simp only [pulseSpatialTest,pulsePairPoint,pulse_boxPoint_zero,mul_comm]
  rw [he] at hh
  exact hh

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorInitialStateBound
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

theorem initialShearedStateBudget_nonneg (Z q0 : ℝ) : 0 ≤ initialShearedStateBudget Z q0 :=
  zero_le_one.trans (le_max_left _ _)

end SmoothLocal.Taylor

end

end OAI
end


