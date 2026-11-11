-- Prove2me | Definitions.Def_Q226II001
-- name    : Q226II001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:35:11.051842+00:00
-- url     : https://prove2.me/theorems/a9fd335f-ba08-4540-b1d9-6d9fa2d75cf4
-- title:
--   Definitions bundle Q226II001 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 448 declarations of OpenAI's Lean: 126 definitions, 1 inductive type or structure and 321 theorems. The definitions and types are `OAI.SmoothLocal.Flow.Reflection.UpperCapMetricJetBudget`, `OAI.SmoothLocal.Flow.Reflection.UpperCapRectangle`, `OAI.SmoothLocal.Flow.Reflection.reflectionMatrix`, `OAI.SmoothLocal.Flow.initialFlowDerivative`, `OAI.SmoothLocal.Flow.initialSecondFlowDerivative`, `OAI.SmoothLocal.Flow.timeSecondFlowDerivative`, `OAI.SmoothLocal.Flow.triangularFlow`, `OAI.SmoothLocal.Flow.triangularLinearEquiv`, `OAI.SmoothLocal.Geometry.IsUnitNormalAt`, `OAI.SmoothLocal.Geometry.MetricFirstJet`, `OAI.SmoothLocal.Geometry.MetricMatrix`, `OAI.SmoothLocal.Geometry.MetricSecondJet`, `OAI.SmoothLocal.Geometry.OrientationLabel`, `OAI.SmoothLocal.Geometry.PlanarAxis`, `OAI.SmoothLocal.Geometry.TensorJetCalculus.coefficient`, `OAI.SmoothLocal.Geometry.accumulatingCenter`, `OAI.SmoothLocal.Geometry.accumulatingDisk`, `OAI.SmoothLocal.Geometry.accumulatingDiskProfile`, `OAI.SmoothLocal.Geometry.accumulatingRadius`, `OAI.SmoothLocal.Geometry.accumulatingScale`, `OAI.SmoothLocal.Geometry.affineTensorCongruence`, `OAI.SmoothLocal.Geometry.affineTensorCongruenceValue`, `OAI.SmoothLocal.Geometry.ambientCross`, `OAI.SmoothLocal.Geometry.axisRotation`, `OAI.SmoothLocal.Geometry.centralBox`, `OAI.SmoothLocal.Geometry.christoffelDerivativeJet`, `OAI.SmoothLocal.Geometry.christoffelJet`, `OAI.SmoothLocal.Geometry.clockwiseAxis`, `OAI.SmoothLocal.Geometry.coordinateCircle`, `OAI.SmoothLocal.Geometry.coordinateCircleVelocity`, `OAI.SmoothLocal.Geometry.coordinateDirections`, `OAI.SmoothLocal.Geometry.curvatureJet`, `OAI.SmoothLocal.Geometry.diskBoundaryNet`, `OAI.SmoothLocal.Geometry.enlargedAccumulatingDisk`, `OAI.SmoothLocal.Geometry.euclideanPlaneCoordinates`, `OAI.SmoothLocal.Geometry.exteriorCenterNet`, `OAI.SmoothLocal.Geometry.exteriorClosedLayer`, `OAI.SmoothLocal.Geometry.exteriorLayerInner`, `OAI.SmoothLocal.Geometry.exteriorLayerMiddle`, `OAI.SmoothLocal.Geometry.exteriorLayerOuter` and 87 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Assembly_AccumulatingDisks`, `IsometricImmersion_Assembly_DiagonalAmplitudes`, `IsometricImmersion_Assembly_FlatPatchSum`, `IsometricImmersion_Assembly_SupportedMetricJets`, `IsometricImmersion_Assembly_TensorSeriesLocality`, `IsometricImmersion_Calculus_AffineHessian`, `IsometricImmersion_Calculus_AffineTensorJetBounds`, `IsometricImmersion_Calculus_CoordinateJetBounds`, `IsometricImmersion_Calculus_CoordinateJetNorm`, `IsometricImmersion_Calculus_CoordinateJetReverseNorm`, `IsometricImmersion_Calculus_MixedCoordinateCalculus`, `IsometricImmersion_Calculus_MovingIntervalCalculus`, `IsometricImmersion_Calculus_QuotientCalculus`, `IsometricImmersion_Calculus_QuotientLowBounds`, `IsometricImmersion_Calculus_ShearMetricJets`, `IsometricImmersion_Calculus_SmoothMetricJet`, `IsometricImmersion_Calculus_VerticalSliceJets`, `IsometricImmersion_Caps_CapGradientTransport`, `IsometricImmersion_Caps_CapInductionData`, `IsometricImmersion_Caps_CapReflectionGeometry`, `IsometricImmersion_Caps_EllipticAbsorption`, `IsometricImmersion_Caps_EllipticCutoff`, `IsometricImmersion_Caps_EllipticCutoffEdge`, `IsometricImmersion_Caps_EllipticGradient`, `IsometricImmersion_Caps_EllipticRatio`, `IsometricImmersion_Caps_EnergyCauchySchwarz`, `IsometricImmersion_Caps_IntegratedCapOverlap`, `IsometricImmersion_Caps_PhysicalCapTransport`, `IsometricImmersion_Caps_UpperCapMetricJets`, `IsometricImmersion_Caps_UpperCapWords`, `IsometricImmersion_Comparison_PulseClosureApproximation`, `IsometricImmersion_Coordinates_AffinePatchSquares`, `IsometricImmersion_Coordinates_ExteriorAnnuli`, `IsometricImmersion_Coordinates_ExteriorCenterNets`, `IsometricImmersion_Coordinates_OrientationNet`, `IsometricImmersion_Coordinates_OrientedCenterNets`, `IsometricImmersion_Coordinates_PatchGeometry`, `IsometricImmersion_Coordinates_RoundDisk`, `IsometricImmersion_Coordinates_ShearSpeedBounds`, `IsometricImmersion_Curvature_AffineCurvature`, `IsometricImmersion_Curvature_CurvatureParameter`, `IsometricImmersion_Curvature_CurvatureParameterJets`, `IsometricImmersion_Curvature_DiskCurvatureProfiles`, `IsometricImmersion_Curvature_InitialCurvature`, `IsometricImmersion_Curvature_MetricCurvatureJet`, `IsometricImmersion_Curvature_PatchCurvatureProfiles`, `IsometricImmersion_Darboux_CurvaturePrincipalPart`, `IsometricImmersion_Darboux_DarbouxJet`, `IsometricImmersion_Darboux_DriftBounds`, `IsometricImmersion_Darboux_MixedDarbouxElimination`, `IsometricImmersion_Darboux_QContainingRectangle`, `IsometricImmersion_Darboux_QPositiveFloor`, `IsometricImmersion_Darboux_QResidualFactors`, `IsometricImmersion_Darboux_QResidualL2`, `IsometricImmersion_Darboux_SixVariableLinearization`, `IsometricImmersion_Energy_ActualRemainderL2`, `IsometricImmersion_Energy_DirectedCoercivity`, `IsometricImmersion_Energy_DirectedCutoffBalance`, `IsometricImmersion_Energy_DirectedDefectCost`, `IsometricImmersion_Energy_DirectedFluxCost`, `IsometricImmersion_Energy_DirectedIntegralEstimate`, `IsometricImmersion_Energy_HyperbolicEnergyDensity`, `IsometricImmersion_Energy_MixedDerivativeL2`, `IsometricImmersion_Energy_MovingEnergyPropagation`, `IsometricImmersion_Energy_MovingHyperbolicEnergy`, `IsometricImmersion_Energy_MovingIntervalSourceL2`, `IsometricImmersion_Energy_MovingSlabEnergy`, `IsometricImmersion_Energy_MultiplierAbsorption`, `IsometricImmersion_Energy_MultiplierIntegral`, `IsometricImmersion_Energy_RegionSobolev`, `IsometricImmersion_Energy_SqrtEnergyGronwall`, `IsometricImmersion_Energy_WeightPrimitive`, `IsometricImmersion_Energy_WeightedMultiplier`, `IsometricImmersion_Estimates_ActualRemainderFactors`, `IsometricImmersion_Estimates_BoundedClassHyperbolicity`, `IsometricImmersion_Estimates_HighFactorOrders`, `IsometricImmersion_Estimates_LargestBlockLinearization`, `IsometricImmersion_Estimates_MixedRemainderFactors`, `IsometricImmersion_Estimates_RemainderAreaBudget`, `IsometricImmersion_Flows_Existence`, `IsometricImmersion_Flows_FlowBounds`, `IsometricImmersion_Flows_FlowInverse`, `IsometricImmersion_Flows_FlowLowBounds`, `IsometricImmersion_Flows_FlowSecondVariation`, `IsometricImmersion_Flows_FlowThirdVariation`, `IsometricImmersion_Flows_FlowTimeVariation`, `IsometricImmersion_Flows_PatchFlowCoercivity`, `IsometricImmersion_Flows_PicardFamily`, `IsometricImmersion_Immersions_ActualHeight`, `IsometricImmersion_Immersions_BoundaryNormal`, `IsometricImmersion_Immersions_BoundedHeightClasses`, `IsometricImmersion_Immersions_NormalField`, `IsometricImmersion_Immersions_RankOneOrientation`, `IsometricImmersion_LocalDomains`, `IsometricImmersion_Metrics_FixedMetricRemainder`, `IsometricImmersion_Metrics_MetricLocality`, `IsometricImmersion_Metrics_MetricPBundleBounds`, `IsometricImmersion_Metrics_ModelCoercivity`, `IsometricImmersion_Metrics_ModelProfile`, `IsometricImmersion_Pulses_CutoffEdgeMoment`, `IsometricImmersion_Pulses_FiniteOscillatoryMoment`, `IsometricImmersion_Pulses_PulseCurvaturePrincipal`, `IsometricImmersion_Pulses_PulseDerivativeBounds`, `IsometricImmersion_Pulses_PulseMomentError`, `IsometricImmersion_Pulses_PulseMomentGeometry`, `IsometricImmersion_Pulses_PulseNeighborhood`, `IsometricImmersion_Pulses_PulseProfiles`, `IsometricImmersion_Pulses_PulseTemporalMoment`, `IsometricImmersion_Pulses_PulseTestEnergy`, `IsometricImmersion_Taylor_ActualDarbouxFaa`, `IsometricImmersion_Taylor_ChainTermDerivative`, `IsometricImmersion_Taylor_ScalarChainExpansion`, `IsometricImmersion_Taylor_TaylorInitialStateBound`, `IsometricImmersion_Volterra_VolterraGlue`, `IsometricImmersion_Volterra_VolterraParameterJets`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`.
--
--   **Imported by** (directly, in this split): the bundles `Q226II003`, `Q226II004`, `Q226II005` and `Q226II006`.
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
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
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

section
-- module Solutions.Q226_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
end OAIVecLookup
end OAICompat434

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_ActualHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff BigOperators
namespace SmoothLocal.Geometry

def IsUnitNormalAt (F : Coord → Ambient) (e : Ambient) (p : Coord) : Prop :=
  inner ℝ e e = 1 ∧ ∀ v, inner ℝ (fderiv ℝ F p v) e = 0

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_NormalField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open WithLp

namespace SmoothLocal.Geometry

def ambientCross (u v : Ambient) : Ambient :=
  toLp 2 (crossProduct (ofLp u) (ofLp v))

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_BoundaryNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def coordinateCircle (center : Coord) (radius : ℝ) (t : ℝ) : Coord :=
  center + radius • ![Real.cos t, Real.sin t]

def coordinateCircleVelocity (radius : ℝ) (t : ℝ) : Coord :=
  radius • ![-Real.sin t, Real.cos t]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_RoundDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Metric

namespace SmoothLocal.Geometry

def roundRadiusSq (center p : Coord) : ℝ :=
  (p 0 - center 0) ^ 2 + (p 1 - center 1) ^ 2

def roundClosedDisk (center : Coord) (radius : ℝ) : Set Coord :=
  {p | roundRadiusSq center p ≤ radius ^ 2}

def roundOpenDisk (center : Coord) (radius : ℝ) : Set Coord :=
  {p | roundRadiusSq center p < radius ^ 2}

def euclideanPlaneCoordinates : Coord ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm

theorem euclideanPlaneCoordinates_dist_sq (p center : Coord) :
    dist (euclideanPlaneCoordinates p) (euclideanPlaneCoordinates center) ^ 2 =
      roundRadiusSq center p := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rfl

theorem roundClosedDisk_eq_preimage_closedBall (center : Coord) {radius : ℝ}
    (hr : 0 ≤ radius) :
    roundClosedDisk center radius = euclideanPlaneCoordinates ⁻¹'
      closedBall (euclideanPlaneCoordinates center) radius := by
  ext p
  change roundRadiusSq center p ≤ radius ^ 2 ↔
    dist (euclideanPlaneCoordinates p) (euclideanPlaneCoordinates center) ≤ radius
  rw [← euclideanPlaneCoordinates_dist_sq]
  exact sq_le_sq₀ dist_nonneg hr

theorem isCompact_roundClosedDisk (center : Coord) {radius : ℝ} (hr : 0 < radius) :
    IsCompact (roundClosedDisk center radius) := by
  rw [roundClosedDisk_eq_preimage_closedBall center hr.le]
  exact euclideanPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr
    (isCompact_closedBall (euclideanPlaneCoordinates center) radius)

theorem mem_frontier_roundClosedDisk_iff (center p : Coord) {radius : ℝ}
    (hr : 0 < radius) :
    p ∈ frontier (roundClosedDisk center radius) ↔ roundRadiusSq center p = radius ^ 2 := by
  rw [roundClosedDisk_eq_preimage_closedBall center hr.le]
  change p ∈ frontier (euclideanPlaneCoordinates.toHomeomorph ⁻¹'
    closedBall (euclideanPlaneCoordinates center) radius) ↔ _
  rw [← euclideanPlaneCoordinates.toHomeomorph.preimage_frontier,
    frontier_closedBall _ hr.ne']
  change dist (euclideanPlaneCoordinates p) (euclideanPlaneCoordinates center) = radius ↔ _
  rw [← sq_eq_sq₀ dist_nonneg hr.le, euclideanPlaneCoordinates_dist_sq]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_AccumulatingDisks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

def accumulatingScale (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

def accumulatingCenter (n : ℕ) : Coord := ![accumulatingScale n, 0]

def accumulatingRadius (n : ℕ) : ℝ := accumulatingScale n / 8

def accumulatingDisk (n : ℕ) : Set Coord :=
  roundClosedDisk (accumulatingCenter n) (accumulatingRadius n)

def enlargedAccumulatingDisk (n : ℕ) : Set Coord :=
  roundClosedDisk (accumulatingCenter n) (2 * accumulatingRadius n)

theorem accumulatingScale_pos (n : ℕ) : 0 < accumulatingScale n := by
  exact pow_pos (by norm_num) _

theorem accumulatingScale_le_half (n : ℕ) : accumulatingScale n ≤ (1 / 2 : ℝ) := by
  exact pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero n)

theorem accumulatingScale_succ (n : ℕ) :
    accumulatingScale (n + 1) = accumulatingScale n / 2 := by
  simp only [accumulatingScale, pow_succ]
  ring

theorem accumulatingScale_antitone : Antitone accumulatingScale := by
  intro m n hmn
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right hmn 1)

theorem accumulatingScale_le_half_of_lt {m n : ℕ} (hmn : m < n) :
    accumulatingScale n ≤ accumulatingScale m / 2 := by
  rw [← accumulatingScale_succ]
  exact accumulatingScale_antitone (Nat.succ_le_of_lt hmn)

theorem accumulatingRadius_pos (n : ℕ) : 0 < accumulatingRadius n :=
  div_pos (accumulatingScale_pos n) (by norm_num)

theorem roundClosedDisk_coord_abs_le (c : Coord) {r : ℝ} (hr : 0 ≤ r)
    {p : Coord} (hp : p ∈ roundClosedDisk c r) (i : Fin 2) : |p i - c i| ≤ r := by
  have hsq : (p i - c i) ^ 2 ≤ r ^ 2 := by
    change (p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 ≤ r ^ 2 at hp
    fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one]
    · nlinarith [sq_nonneg (p 1 - c 1)]
    · nlinarith [sq_nonneg (p 0 - c 0)]
  apply (sq_le_sq₀ (abs_nonneg _) hr).mp
  simpa only [sq_abs] using hsq

theorem accumulatingDisk_subset_enlarged (n : ℕ) :
    accumulatingDisk n ⊆ enlargedAccumulatingDisk n := by
  intro p hp
  change roundRadiusSq (accumulatingCenter n) p ≤ (accumulatingRadius n) ^ 2 at hp
  change roundRadiusSq (accumulatingCenter n) p ≤ (2 * accumulatingRadius n) ^ 2
  nlinarith [sq_nonneg (accumulatingRadius n)]

theorem enlargedAccumulatingDisk_bounds (n : ℕ) {p : Coord}
    (hp : p ∈ enlargedAccumulatingDisk n) :
    (3 / 4 : ℝ) * accumulatingScale n ≤ p 0 ∧
      p 0 ≤ (5 / 4 : ℝ) * accumulatingScale n ∧
      |p 1| ≤ accumulatingScale n / 4 := by
  have hr : 0 ≤ 2 * accumulatingRadius n :=
    (mul_pos (by norm_num) (accumulatingRadius_pos n)).le
  have hx := roundClosedDisk_coord_abs_le (accumulatingCenter n) hr hp 0
  have hy := roundClosedDisk_coord_abs_le (accumulatingCenter n) hr hp 1
  simp only [accumulatingCenter, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_zero, accumulatingRadius] at hx hy
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx
  refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem enlargedAccumulatingDisk_disjoint_of_lt {m n : ℕ} (hmn : m < n) :
    Disjoint (enlargedAccumulatingDisk m) (enlargedAccumulatingDisk n) := by
  apply Set.disjoint_left.mpr
  intro p hpm hpn
  have hm := enlargedAccumulatingDisk_bounds m hpm
  have hn := enlargedAccumulatingDisk_bounds n hpn
  have hscale := accumulatingScale_le_half_of_lt hmn
  have hpos := accumulatingScale_pos m
  linarith

theorem enlargedAccumulatingDisks_pairwise_disjoint :
    Pairwise (fun m n => Disjoint (enlargedAccumulatingDisk m) (enlargedAccumulatingDisk n)) := by
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact enlargedAccumulatingDisk_disjoint_of_lt hlt
  · exact (enlargedAccumulatingDisk_disjoint_of_lt hgt).symm

theorem accumulatingDisks_pairwise_disjoint :
    Pairwise (fun m n => Disjoint (accumulatingDisk m) (accumulatingDisk n)) := by
  intro m n hmn
  exact (enlargedAccumulatingDisks_pairwise_disjoint hmn).mono
    (accumulatingDisk_subset_enlarged m) (accumulatingDisk_subset_enlarged n)

theorem enlargedAccumulatingDisk_subset_square (n : ℕ) : enlargedAccumulatingDisk n ⊆ square := by
  intro p hp i
  have hb := enlargedAccumulatingDisk_bounds n hp
  have hpos := accumulatingScale_pos n
  have hhalf := accumulatingScale_le_half n
  fin_cases i
  · change -1 < p 0 ∧ p 0 < 1
    constructor <;> linarith
  · change -1 < p 1 ∧ p 1 < 1
    obtain ⟨hylo, hyhi⟩ := abs_le.mp hb.2.2
    constructor <;> linarith

theorem accumulatingDisk_isCompact (n : ℕ) : IsCompact (accumulatingDisk n) :=
  isCompact_roundClosedDisk (accumulatingCenter n) (accumulatingRadius_pos n)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_FlatPatchSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set

namespace SmoothLocal.Geometry

def patchSeriesWeight (ε : ℝ) (n : ℕ) : ℝ := ε / 2 / (2 : ℝ) ^ n

theorem patchSeriesWeight_hasSum (ε : ℝ) : HasSum (patchSeriesWeight ε) ε :=
  hasSum_geometric_two' ε

theorem patchSeriesWeight_pos {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 < patchSeriesWeight ε n := by
  unfold patchSeriesWeight
  positivity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def flatPatchSum (f : ℕ → Coord → V) (p : Coord) : V := ∑' n, f n p

omit [CompleteSpace V] in
theorem compactSmooth_has_derivative_bounds (f : Coord → V)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (k : ℕ) :
    ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ k f p‖ ≤ C :=
  (hf.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).bounded_above_of_compact_support
    (hc.iteratedFDeriv k)

omit [CompleteSpace V] in
theorem exists_summable_derivative_majorant (f : ℕ → Coord → V) (ε : ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (hbound : ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (f n) p‖ ≤ patchSeriesWeight ε n) :
    ∃ v : ℕ → ℕ → ℝ, (∀ k, Summable (v k)) ∧
      ∀ k n p, ‖iteratedFDeriv ℝ k (f n) p‖ ≤ v k n := by
  classical
  have hC (k n : ℕ) : ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ k (f n) p‖ ≤ C :=
    compactSmooth_has_derivative_bounds (f n) (hf n) (hc n) k
  choose C hC using hC
  let v : ℕ → ℕ → ℝ := fun k n => if k ≤ n then patchSeriesWeight ε n else C k n
  refine ⟨v, ?_, ?_⟩
  · intro k
    apply (patchSeriesWeight_hasSum ε).summable.congr_atTop
    filter_upwards [eventually_ge_atTop k] with n hn
    simp only [v, ite_eq_left hn]
  · intro k n p
    by_cases hkn : k ≤ n
    · simpa only [v, ite_eq_left hkn] using hbound n k hkn p
    · simpa only [v, ite_eq_right hkn] using hC k n p

omit [CompleteSpace V] in
theorem flatPatchSum_norm_le (f : ℕ → Coord → V) (ε : ℝ)
    (hbound : ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (f n) p‖ ≤ patchSeriesWeight ε n) (p : Coord) :
    ‖flatPatchSum f p‖ ≤ ε := by
  apply tsum_of_norm_bounded (patchSeriesWeight_hasSum ε)
  intro n
  simpa only [norm_iteratedFDeriv_zero] using hbound n 0 (Nat.zero_le n) p

theorem flatPatchSum_contDiff (f : ℕ → Coord → V) (ε : ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (hbound : ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (f n) p‖ ≤ patchSeriesWeight ε n) :
    ContDiff ℝ ∞ (flatPatchSum f) := by
  obtain ⟨v, hv, hfv⟩ := exists_summable_derivative_majorant f ε hf hc hbound
  exact contDiff_tsum (N := ⊤) hf (fun k _ => hv k) (fun k n p _ => hfv k n p)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_DiagonalAmplitudes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set

namespace SmoothLocal.Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem exists_positive_diagonal_amplitudes (f : ℕ → Coord → V)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧
      ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun q => δ n • f n q) p‖ ≤ patchSeriesWeight ε n := by
  classical
  have hC (k n : ℕ) : ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ k (f n) p‖ ≤ C :=
    compactSmooth_has_derivative_bounds (f n) (hf n) (hc n) k
  choose C hC using hC
  let D : ℕ → ℝ := fun n => 1 + ∑ k ∈ Finset.range (n + 1), |C k n|
  have hD (n : ℕ) : 0 < D n := by
    have hs : 0 ≤ ∑ k ∈ Finset.range (n + 1), |C k n| :=
      Finset.sum_nonneg (fun k _ => abs_nonneg (C k n))
    dsimp [D]
    linarith
  have hCD (n k : ℕ) (hkn : k ≤ n) : C k n ≤ D n := by
    have hk : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hkn)
    have hs : |C k n| ≤ ∑ j ∈ Finset.range (n + 1), |C j n| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (C j n)) hk
    dsimp [D]
    linarith [le_abs_self (C k n)]
  let δ : ℕ → ℝ := fun n => patchSeriesWeight ε n / D n
  have hδ (n : ℕ) : 0 < δ n := div_pos (patchSeriesWeight_pos hε n) (hD n)
  refine ⟨δ, hδ, ?_⟩
  intro n k hkn p
  have hfn : ContDiffAt ℝ k (f n) p :=
    (hf n).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDeriv_const_smul_apply' hfn,
    norm_smul, Real.norm_of_nonneg (hδ n).le]
  calc
    δ n * ‖iteratedFDeriv ℝ k (f n) p‖ ≤ δ n * D n :=
      mul_le_mul_of_nonneg_left ((hC k n p).trans (hCD n k hkn)) (hδ n).le
    _ = patchSeriesWeight ε n := div_mul_cancel₀ _ (hD n).ne'

omit [CompleteSpace V] in
theorem tsupport_const_smul_eq_of_pos (f : Coord → V) {δ : ℝ} (hδ : 0 < δ) :
    tsupport (fun p => δ • f p) = tsupport f := by
  change closure (Function.support (δ • f)) = closure (Function.support f)
  rw [Function.support_const_smul_of_ne_zero δ f hδ.ne']

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open scoped Matrix.Norms.Elementwise
open Filter

namespace SmoothLocal.Geometry

theorem eventuallyEq_zero_of_not_mem_tsupport
    {V : Type*} [Zero V] (f : Coord → V) {p : Coord} (hp : p ∉ tsupport f) :
    f =ᶠ[𝓝 p] 0 := by
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hp] with q hq
  change f q = 0
  by_contra hne
  exact hq (subset_tsupport f hne)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_ModelProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Model
open SmoothLocal.Geometry

def squareTransition (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 1)

theorem squareTransition_contDiff : ContDiff ℝ ∞ squareTransition :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem squareTransition_range (t : ℝ) :
    0 ≤ squareTransition t ∧ squareTransition t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem squareTransition_zero {t : ℝ} (ht : t ≤ 1 / 4) : squareTransition t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem squareTransition_one {t : ℝ} (ht : 1 / 2 ≤ t) : squareTransition t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem squareTransition_monotone : Monotone squareTransition := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

theorem squareTransition_deriv_nonneg (t : ℝ) : 0 ≤ deriv squareTransition t :=
  squareTransition_monotone.deriv_nonneg

def modelProfile (y : ℝ) : ℝ := 1 - y ^ 2 * squareTransition (y ^ 2)

theorem modelProfile_contDiff : ContDiff ℝ ∞ modelProfile :=
  contDiff_const.sub ((contDiff_id.pow 2).mul
    (squareTransition_contDiff.comp (contDiff_id.pow 2)))

theorem modelProfile_even : Function.Even modelProfile := by
  intro y
  simp [modelProfile]

theorem modelProfile_bounds (y : ℝ) : 1 - y ^ 2 ≤ modelProfile y ∧ modelProfile y ≤ 1 := by
  have hh := squareTransition_range (y ^ 2)
  have hprod := mul_le_mul_of_nonneg_left hh.2 (sq_nonneg y)
  have hprod0 := mul_nonneg (sq_nonneg y) hh.1
  unfold modelProfile
  constructor <;> nlinarith

theorem modelProfile_eq_one_sub_sq {y : ℝ} (hy : 1 / 2 ≤ y ^ 2) :
    modelProfile y = 1 - y ^ 2 := by
  simp [modelProfile, squareTransition_one hy]

theorem modelProfile_hasDerivAt (y : ℝ) :
    HasDerivAt modelProfile
      (-2 * y * squareTransition (y ^ 2) - 2 * y ^ 3 * deriv squareTransition (y ^ 2)) y := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    convert (hasDerivAt_id y).pow 2 using 1 <;> first | rfl | simp
  have hcut := ((squareTransition_contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (y ^ 2)).hasDerivAt.comp y hsq
  have hp := (hsq.mul hcut).const_sub 1
  convert hp using 1 <;> first | rfl | (dsimp only [Function.comp_def]; ring)

theorem modelProfile_deriv (y : ℝ) :
    deriv modelProfile y =
      -2 * y * squareTransition (y ^ 2) - 2 * y ^ 3 * deriv squareTransition (y ^ 2) :=
  (modelProfile_hasDerivAt y).deriv

def modelCurvature (kappa : ℝ) (p : Coord) : ℝ :=
  kappa * ((p 0) ^ 2 - modelProfile (p 1))

theorem modelCurvature_contDiff (kappa : ℝ) : ContDiff ℝ ∞ (modelCurvature kappa) :=
  contDiff_const.mul (((contDiff_apply ℝ ℝ 0).pow 2).sub
    (modelProfile_contDiff.comp (contDiff_apply ℝ ℝ 1)))

theorem modelCurvature_lateral_band_lower {kappa : ℝ} (hkappa : 0 < kappa) {p : Coord}
    (hp : 3 / 2 < |p 0|) : 5 / 4 * kappa < modelCurvature kappa p := by
  have hx : (3 / 2 : ℝ) ^ 2 < (p 0) ^ 2 := sq_lt_sq.mpr (by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    exact hp)
  have hmul := mul_lt_mul_of_pos_left hx hkappa
  have hh := mul_le_mul_of_nonneg_left (modelProfile_bounds (p 1)).2 hkappa.le
  unfold modelCurvature
  nlinarith

end SmoothLocal.Model

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_PatchGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Model

def patchBox : Set Coord :=
  Icc (fun _ => (-(1 / 10 : ℝ))) (fun _ => (1 / 10 : ℝ))

def centralBox : Set Coord :=
  Icc (fun _ => (-(1 / 5 : ℝ))) (fun _ => (1 / 5 : ℝ))

theorem patchBox_subset_centralBox : patchBox ⊆ centralBox := by
  intro p hp
  constructor <;> intro i <;> linarith [hp.1 i, hp.2 i]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_AffineHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

theorem matrix_column_basis_expansion (R : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    R *ᵥ Pi.single i (1 : ℝ) =
      R 0 i • Pi.single 0 (1 : ℝ) + R 1 i • Pi.single 1 (1 : ℝ) := by
  rw [Matrix.mulVec_single_one]
  funext k
  fin_cases k <;> simp

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_AffineCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace AffineCalculus

theorem pushed_connection_product
    (R : Matrix (Fin 2) (Fin 2) ℝ)
    (C D : Fin 2 → Fin 2 → Fin 2 → ℝ)
    (h : ∀ a i j, (∑ l, R a l * C l i j) = ∑ c, ∑ d, R c i * R d j * D a c d)
    (a i j k : Fin 2) :
    (∑ l, R a l * ∑ m, C m j k * C l i m) =
      ∑ c, ∑ d, ∑ e, ∑ f, R c i * R e j * R f k * D d e f * D a c d := by
  calc
    _ = ∑ m, C m j k * (∑ l, R a l * C l i m) := by
      simp only [Fin.sum_univ_two]
      ring
    _ = ∑ m, C m j k * (∑ c, ∑ d, R c i * R d m * D a c d) := by
      simp only [h]
    _ = ∑ c, ∑ d, R c i * D a c d * (∑ m, R d m * C m j k) := by
      simp only [Fin.sum_univ_two]
      ring
    _ = ∑ c, ∑ d, R c i * D a c d *
        (∑ e, ∑ f, R e j * R f k * D d e f) := by simp only [h]
    _ = _ := by simp only [Fin.sum_univ_two] <;> ring

end AffineCalculus

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_Existence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric
open scoped NNReal Interval

namespace SmoothLocal.ODE

def curvatureField (k : ℝ → ℝ) (t : ℝ) (u : ℝ × ℝ) : ℝ × ℝ :=
  (u.2, -k t * u.1)

theorem curvatureField_lipschitz {k : ℝ → ℝ} {t : ℝ}
    (hk : |k t| ≤ (1 : ℝ) / 1000) :
    LipschitzWith 1 (curvatureField k t) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  change max ‖u.2 - v.2‖ ‖-k t * u.1 - -k t * v.1‖ ≤ ‖u - v‖
  refine max_le (norm_snd_le (u - v)) ?_
  calc
    ‖-k t * u.1 - -k t * v.1‖ = |k t| * ‖u.1 - v.1‖ := by
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_neg]
    _ ≤ 1 * ‖u.1 - v.1‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ ‖u - v‖ := by simpa using norm_fst_le (u - v)

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_CurvatureParameter
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

theorem compact_x_mem_square_interval {r : ℝ} (hr1 : r < 1)
    (x : Icc (-r) r) : (x : ℝ) ∈ Ioo (-1 : ℝ) 1 :=
  ⟨(neg_lt_neg hr1).trans_le x.2.1, x.2.2.trans_lt hr1⟩

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Volterra_VolterraParameterJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

theorem iteratedDeriv_contDiffOn_of_isOpen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} (hs : IsOpen s) {F : ℝ → E} (hF : ContDiffOn ℝ ∞ F s) :
    ∀ n, ContDiffOn ℝ ∞ (iteratedDeriv n F) s := by
  intro n
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hF
  | succ n hn =>
      rw [iteratedDeriv_succ]
      exact hn.deriv_of_isOpen hs (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

theorem iteratedDeriv_clm_comp
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {f : ℝ → E} {y : ℝ} (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f y) :
    iteratedDeriv n (fun t => L (f t)) y = L (iteratedDeriv n f y) := by
  change iteratedFDeriv ℝ n (L ∘ f) y (fun _ => 1) = _
  rw [L.iteratedFDeriv_comp_left hf (WithTop.coe_le_coe.mpr le_top)]
  rfl

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_CurvatureParameterJets
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

theorem iteratedDeriv_eq_of_derivative_sequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} (hs : IsOpen s) (H : ℕ → ℝ → E)
    (hd : ∀ n y, y ∈ s → HasDerivAt (H n) (H (n + 1) y) y) :
    ∀ n y, y ∈ s → iteratedDeriv n (H 0) y = H n y := by
  intro n
  induction n with
  | zero => intro y hy; simp only [iteratedDeriv_zero]
  | succ n hn =>
      intro y hy
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv n (H 0) =ᶠ[𝓝 y] H n := by
        filter_upwards [hs.mem_nhds hy] with t ht
        exact hn t ht
      exact ((hd n y hy).congr_of_eventuallyEq hev).deriv

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Volterra_VolterraGlue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric
open scoped ContDiff NNReal Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

def interiorRadius (x : ℝ) : ℝ := (|x| + 1) / 2

theorem interiorRadius_pos (x : ℝ) : 0 < interiorRadius x := by
  unfold interiorRadius
  linarith [abs_nonneg x]

theorem interiorRadius_lt_one {x : ℝ} (hx : |x| < 1) : interiorRadius x < 1 := by
  unfold interiorRadius
  linarith

theorem abs_lt_interiorRadius {x : ℝ} (hx : |x| < 1) : |x| < interiorRadius x := by
  unfold interiorRadius
  linarith

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_MetricCurvatureJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

abbrev MetricMatrix := Matrix (Fin 2) (Fin 2) ℝ
abbrev MetricFirstJet := Fin 2 → MetricMatrix
abbrev MetricSecondJet := Fin 2 → Fin 2 → MetricMatrix

def inverseDerivativeJet (G : MetricMatrix) (D : MetricFirstJet)
    (d i j : Fin 2) : ℝ :=
  -(∑ a, ∑ b, G⁻¹ i a * D d a b * G⁻¹ b j)

def christoffelJet (G : MetricMatrix) (D : MetricFirstJet) (k i j : Fin 2) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, G⁻¹ k l * (D i j l + D j i l - D l i j)

def christoffelDerivativeJet (G : MetricMatrix) (D : MetricFirstJet)
    (DD : MetricSecondJet) (d k i j : Fin 2) : ℝ :=
  (1 / 2 : ℝ) * ∑ l,
    (inverseDerivativeJet G D d k l * (D i j l + D j i l - D l i j) +
      G⁻¹ k l * (DD d i j l + DD d j i l - DD d l i j))

def riemannJet (G : MetricMatrix) (D : MetricFirstJet)
    (DD : MetricSecondJet) (l k i j : Fin 2) : ℝ :=
  christoffelDerivativeJet G D DD i l j k -
    christoffelDerivativeJet G D DD j l i k +
    ∑ m, (christoffelJet G D m j k * christoffelJet G D l i m -
      christoffelJet G D m i k * christoffelJet G D l j m)

def curvatureJet (G : MetricMatrix) (D : MetricFirstJet) (DD : MetricSecondJet) : ℝ :=
  (∑ l, G 0 l * riemannJet G D DD l 1 0 1) / G.det

section Continuity
variable {T : Type*} [TopologicalSpace T] {t : T}
variable {G : T → MetricMatrix} {D : T → MetricFirstJet} {DD : T → MetricSecondJet}

theorem metricMatrix_inverse_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t) (hdet : (G t).det ≠ 0)
    (i j : Fin 2) : ContinuousAt (fun s => (G s)⁻¹ i j) t := by
  have hdetc : ContinuousAt (fun s => (G s).det) t := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  have hi := hdetc.inv₀ hdet
  have ha : ContinuousAt (fun s => (G s).adjugate i j) t := by
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_two] using hG 1 1
    · convert (hG 0 1).neg using 1
      all_goals try with_reducible_and_instances rfl
      funext s
      simp [Matrix.adjugate_fin_two]
    · convert (hG 1 0).neg using 1
      all_goals try with_reducible_and_instances rfl
      funext s
      simp [Matrix.adjugate_fin_two]
    · simpa [Matrix.adjugate_fin_two] using hG 0 0
  have hh : ContinuousAt (fun s => (G s).det⁻¹ * (G s).adjugate i j) t := hi.mul ha
  simpa [Matrix.inv_def, Ring.inverse_eq_inv, smul_eq_mul] using hh

theorem inverseDerivativeJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hdet : (G t).det ≠ 0) (d i j : Fin 2) :
    ContinuousAt (fun s => inverseDerivativeJet (G s) (D s) d i j) t := by
  have hi := metricMatrix_inverse_continuousAt hG hdet
  simp only [inverseDerivativeJet, Fin.sum_univ_two]
  fun_prop

theorem christoffelJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hdet : (G t).det ≠ 0) (k i j : Fin 2) :
    ContinuousAt (fun s => christoffelJet (G s) (D s) k i j) t := by
  have hi := metricMatrix_inverse_continuousAt hG hdet
  simp only [christoffelJet, Fin.sum_univ_two]
  fun_prop

theorem christoffelDerivativeJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContinuousAt (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) (d k i j : Fin 2) :
    ContinuousAt (fun s => christoffelDerivativeJet (G s) (D s) (DD s) d k i j) t := by
  have hi := metricMatrix_inverse_continuousAt hG hdet
  have hdi := inverseDerivativeJet_continuousAt hG hD hdet
  simp only [christoffelDerivativeJet, Fin.sum_univ_two]
  fun_prop

theorem riemannJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContinuousAt (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) (l k i j : Fin 2) :
    ContinuousAt (fun s => riemannJet (G s) (D s) (DD s) l k i j) t := by
  have hΓ := christoffelJet_continuousAt hG hD hdet
  have hDΓ := christoffelDerivativeJet_continuousAt hG hD hDD hdet
  simp only [riemannJet, Fin.sum_univ_two]
  fun_prop

theorem curvatureJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContinuousAt (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) :
    ContinuousAt (fun s => curvatureJet (G s) (D s) (DD s)) t := by
  have hR := riemannJet_continuousAt hG hD hDD hdet
  have hn : ContinuousAt (fun s => ∑ l, G s 0 l * riemannJet (G s) (D s) (DD s) l 1 0 1) t := by
    simp only [Fin.sum_univ_two]
    fun_prop
  have hd : ContinuousAt (fun s => (G s).det) t := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  exact hn.div hd hdet

end Continuity
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

def metricCoefficientCLM (i j : Fin 2) : MetricMatrix →L[ℝ] ℝ where
  toFun A := A i j
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  cont := (continuous_apply j).comp (continuous_apply i)

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_QuotientCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

variable {f h : Coord → ℝ} {p : Coord} {U : Set Coord}

theorem quotient_contDiffOn
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U)
    (hne : ∀ p ∈ U, h p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => f p / h p) U := by
  exact hf.div hh hne

theorem height_energy_quotient_pos (E h : ℝ) (hE : 0 < E) (hh : h ≠ 0) :
    0 < E / h ^ 2 :=
  div_pos hE (sq_pos_of_ne_zero hh)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_QuotientLowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry.LowQuotient

theorem abs_add_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x + y| ≤ A + B := (abs_add_le x y).trans (add_le_add hx hy)

theorem abs_mul_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) (hA : 0 ≤ A) :
    |x * y| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) hA

theorem abs_sub_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x - y| ≤ A + B := (abs_sub x y).trans (add_le_add hx hy)

theorem abs_div_bound {x y N c : ℝ} (hN : 0 ≤ N) (hnum : |x| ≤ N)
    (hc : 0 < c) (hden : c ≤ |y|) : |x / y| ≤ N / c := by
  rw [abs_div]
  exact div_le_div₀ hN hnum hc hden

variable {U : Set Coord} {a b : Coord → ℝ} {M c : ℝ}

theorem denominator_ne_zero (hc : 0 < c) (hden : ∀ p ∈ U, c ≤ |b p|) :
    ∀ p ∈ U, b p ≠ 0 := by
  intro p hp hzero
  have hh := hden p hp
  rw [hzero, abs_zero] at hh
  linarith

end SmoothLocal.Geometry.LowQuotient

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_CoordinateJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

namespace CoordinateBound

theorem abs_add_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x + y| ≤ A + B := (abs_add_le x y).trans (add_le_add hx hy)

end CoordinateBound
end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_CoordinateJetNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

def coordinateDirections : (ds : List (Fin 2)) → Fin ds.length → Coord
  | [] => fun _ => 0
  | i :: ds => Fin.cons (Pi.single i 1) (coordinateDirections ds)

theorem coordinateDirections_norm (ds : List (Fin 2)) (k : Fin ds.length) :
    ‖coordinateDirections ds k‖ = 1 := by
  induction ds with
  | nil => exact Fin.elim0 k
  | cons i ds ih =>
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [coordinateDirections, Pi.norm_single]
    · simpa only [coordinateDirections, Fin.cons_succ] using ih j

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_TensorSeriesLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry

namespace TensorJetCalculus

def coefficient (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))

end TensorJetCalculus

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_AffineTensorJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

def affineTensorCongruenceValue
    (R A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := R⁻¹ᵀ * A * R⁻¹

theorem affineTensorCongruenceValue_add
    (R A B : Matrix (Fin 2) (Fin 2) ℝ) :
    affineTensorCongruenceValue R (A+B) =
      affineTensorCongruenceValue R A + affineTensorCongruenceValue R B := by
  simp only [affineTensorCongruenceValue, Matrix.mul_add, Matrix.add_mul]

theorem affineTensorCongruenceValue_smul
    (R A : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) :
    affineTensorCongruenceValue R (c • A) = c • affineTensorCongruenceValue R A := by
  simp only [affineTensorCongruenceValue, Matrix.mul_smul, Matrix.smul_mul]

def affineTensorCongruence (R : Matrix (Fin 2) (Fin 2) ℝ) :
    (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := affineTensorCongruenceValue R
      map_add' := affineTensorCongruenceValue_add R
      map_smul' := fun c A => affineTensorCongruenceValue_smul R A c }

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_DarbouxJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def jetDriftVector (q : ℝ) : Coord := ![1, -q]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_HighFactorOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace SmoothLocal.HighEquation

theorem ordered_partSize_sum {ell : ℕ} (c : OrderedFinpartition ell) :
    ∑ j, c.partSize j = ell := by
  have hh := Fintype.card_congr c.equivSigma
  simpa only [Fintype.card_sigma, Fintype.card_fin] using hh

theorem ordered_two_partSizes_le {ell : ℕ} (c : OrderedFinpartition ell)
    {i j : Fin c.length} (hij : i ≠ j) :
    c.partSize i + c.partSize j ≤ ell := by
  have hh : ∑ k ∈ ({i, j} : Finset (Fin c.length)), c.partSize k ≤
      ∑ k, c.partSize k :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  simpa only [Finset.sum_pair hij, ordered_partSize_sum] using hh

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_ActualDarbouxFaa
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem verticalPoint_contDiff (x : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ => (![x, y] : Coord)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_id

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_VerticalSliceJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem verticalPoint_hasDerivAt (x y : ℝ) :
    HasDerivAt (fun t : ℝ => (![x, t] : Coord)) (Pi.single 1 (1 : ℝ)) y := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa using hasDerivAt_const y x
  · convert hasDerivAt_id y using 1 <;> rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_DriftBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Geometry

theorem explicitDriftError_scalar_bound
    (h E hy T J c BE Bh BT BJ : ℝ)
    (hc : 0 < c) (hh : c ≤ |h|)
    (hE : |E| ≤ BE) (hhy : |hy| ≤ Bh)
    (hT : |T| ≤ BT) (hJ : |J| ≤ BJ) :
    |E / h ^ 2 * (T - hy / h) + J / h| ≤
      BE / c ^ 2 * (BT + Bh / c) + BJ / c := by
  have hBE : 0 ≤ BE := (abs_nonneg E).trans hE
  have hBh : 0 ≤ Bh := (abs_nonneg hy).trans hhy
  have hBJ : 0 ≤ BJ := (abs_nonneg J).trans hJ
  have hEh : |E / h ^ 2| ≤ BE / c ^ 2 := by
    rw [abs_div, abs_pow]
    exact div_le_div₀ hBE hE (sq_pos_of_pos hc) (pow_le_pow_left₀ hc.le hh 2)
  have hhyh : |hy / h| ≤ Bh / c := by
    rw [abs_div]
    exact div_le_div₀ hBh hhy hc hh
  have hJh : |J / h| ≤ BJ / c := by
    rw [abs_div]
    exact div_le_div₀ hBJ hJ hc hh
  have htri : |T - hy / h| ≤ |T| + |hy / h| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le T (-(hy / h))
  have hsub : |T - hy / h| ≤ BT + Bh / c :=
    htri.trans (add_le_add hT hhyh)
  calc
    |E / h ^ 2 * (T - hy / h) + J / h|
        ≤ |E / h ^ 2 * (T - hy / h)| + |J / h| := abs_add_le _ _
    _ = |E / h ^ 2| * |T - hy / h| + |J / h| := by rw [abs_mul]
    _ ≤ BE / c ^ 2 * (BT + Bh / c) + BJ / c :=
      add_le_add
        (mul_le_mul hEh hsub (abs_nonneg _) (div_nonneg hBE (sq_nonneg c))) hJh

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_SixVariableLinearization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem fderiv_axis_eq_deriv_update {n : ℕ} {f : (Fin n → ℝ) → ℝ} {w : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f w) (i : Fin n) :
    fderiv ℝ f w (Pi.single i 1) = deriv (fun t => f (Function.update w i t)) (w i) := by
  have hd : HasFDerivAt f (fderiv ℝ f w) (Function.update w i (w i)) := by
    simpa using hf.hasFDerivAt
  exact (hd.comp_hasDerivAt (w i) (hasDerivAt_update w i (w i))).deriv.symm

def gradientStateIndex (i : Fin 2) : Fin 6 := if i = 0 then 2 else 3

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_LargestBlockLinearization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def fullBlockPartition (ell : ℕ) (hell : 0 < ell) : OrderedFinpartition ell where
  length := 1
  partSize _ := ell
  partSize_pos _ := hell
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := by
    intro firstBlock _ secondBlock _ hne
    exact (hne (Subsingleton.elim firstBlock secondBlock)).elim
  cover i := ⟨0, i, rfl⟩

theorem ordered_full_size_length_one {ell : ℕ} (c : OrderedFinpartition ell)
    {i : Fin c.length} (hi : c.partSize i = ell) : c.length = 1 := by
  have hunique : ∀ j : Fin c.length, j = i := by
    intro j
    by_contra hji
    have hb := ordered_two_partSizes_le c hji
    have hj := c.partSize_pos j
    rw [hi] at hb
    omega
  have hsub : Subsingleton (Fin c.length) :=
    ⟨fun a b => (hunique a).trans (hunique b).symm⟩
  have hcard := Fintype.card_le_one_iff_subsingleton.mpr hsub
  simp only [Fintype.card_fin] at hcard
  have hi0 := i.isLt
  omega

theorem ordered_length_one_eq_full {ell : ℕ} (hell : 0 < ell)
    (c : OrderedFinpartition ell) (hc : c.length = 1) : c = fullBlockPartition ell hell := by
  rcases c with ⟨length, size, hpos, emb, hmono, horder, hdis, hcover⟩
  dsimp only at hc
  subst length
  have hsize0 : size 0 = ell := by
    have hh := ordered_partSize_sum
      (OrderedFinpartition.mk 1 size hpos emb hmono horder hdis hcover)
    simpa only [Fin.sum_univ_one] using hh
  have hsize : size = fun _ : Fin 1 => ell := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using hsize0
  subst size
  have hemb : emb = fun _ : Fin 1 => (id : Fin ell → Fin ell) := by
    funext i
    exact (hmono i).eq_id
  subst emb
  rfl

theorem ordered_nonfull_partSize_le {ell : ℕ} (hell : 0 < ell)
    (c : OrderedFinpartition ell) (hc : c ≠ fullBlockPartition ell hell) (i : Fin c.length) :
    c.partSize i ≤ ell - 1 := by
  have hle := c.partSize_le i
  have hne : c.partSize i ≠ ell := by
    intro he
    exact hc (ordered_length_one_eq_full hell c (ordered_full_size_length_one c he))
  omega

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MultiplierAbsorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SmoothLocal.Weighted

theorem normalized_T_lower_bound {H Is epsilon t B MI Mt MB : ℝ}
    (heps : 0 ≤ epsilon) (hMt : 0 ≤ Mt) (hIs : |Is| ≤ MI)
    (ht : |t| ≤ Mt) (hB : |B| ≤ MB)
    (hbudget : 2 * (MI + epsilon + epsilon * Mt * MB) ≤ H) :
    H / 4 ≤ (H - Is - epsilon + epsilon * t * B) / 2 := by
  have hprod : |epsilon * t * B| ≤ epsilon * Mt * MB := by
    rw [abs_mul, abs_mul, abs_of_nonneg heps]
    exact mul_le_mul (mul_le_mul_of_nonneg_left ht heps) hB
      (abs_nonneg B) (mul_nonneg heps hMt)
  have hlower := (abs_le.mp hprod).1
  have hupper := (abs_le.mp hIs).2
  linarith

theorem quadratic_cross_absorption {T S J u v : ℝ} (hT : 0 < T) :
    T / 2 * u ^ 2 + (S - J ^ 2 / (2 * T)) * v ^ 2 ≤
      T * u ^ 2 + S * v ^ 2 + J * u * v := by
  have hs : 0 ≤ (T * u + J * v) ^ 2 / (2 * T) :=
    div_nonneg (sq_nonneg _) (by positivity)
  have he : T * u ^ 2 + S * v ^ 2 + J * u * v -
      (T / 2 * u ^ 2 + (S - J ^ 2 / (2 * T)) * v ^ 2) =
      (T * u + J * v) ^ 2 / (2 * T) := by
    field_simp
    ring
  linarith

theorem cross_loss_bound {T J W H A C epsilon : ℝ}
    (hW : 0 < W) (hH : 0 < H) (hC : 0 ≤ C) (heps : 0 ≤ epsilon)
    (hT : W * H / 4 ≤ T)
    (hJ : |J| ≤ W * C * epsilon * (1 + H * |A|)) :
    J ^ 2 / (T * W) ≤
      8 * C ^ 2 * epsilon ^ 2 * (H⁻¹ + H * A ^ 2) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hmajor : 0 ≤ W * C * epsilon * (1 + H * |A|) := by positivity
  have hj2 : J ^ 2 ≤ (W * C * epsilon * (1 + H * |A|)) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg J) hmajor).mpr hJ
  have hshape : (1 + H * |A|) ^ 2 ≤ 2 * (1 + H ^ 2 * A ^ 2) := by
    nlinarith [sq_nonneg (H * |A| - 1), sq_abs A]
  have hnum : J ^ 2 ≤ 2 * W ^ 2 * C ^ 2 * epsilon ^ 2 * (1 + H ^ 2 * A ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hshape (sq_nonneg (W * C * epsilon))
    nlinarith [hj2]
  have hden : W ^ 2 * H / 4 ≤ T * W := by
    have hm := mul_le_mul_of_nonneg_right hT hW.le
    nlinarith [hm]
  have hR : 0 ≤ 8 * C ^ 2 * epsilon ^ 2 * (H⁻¹ + H * A ^ 2) := by positivity
  apply (div_le_iff₀ (mul_pos hTpos hW)).mpr
  have hm := mul_le_mul_of_nonneg_left hden hR
  have he : (8 * C ^ 2 * epsilon ^ 2 * (H⁻¹ + H * A ^ 2)) *
      (W ^ 2 * H / 4) =
      2 * W ^ 2 * C ^ 2 * epsilon ^ 2 * (1 + H ^ 2 * A ^ 2) := by
    field_simp
    ring
  rw [he] at hm
  exact hnum.trans hm

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_WeightedMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def edgeDistance (b : ℝ) (p : Coord) : ℝ := b - p 1

def weightPhase (lambda : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  -lambda * p 1 + I p

def directedWeight (b lambda : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  (edgeDistance b p) ^ 8 * Real.exp (weightPhase lambda I p)

def directedM (b lambda : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  -directedWeight b lambda I p

def directedN (b lambda epsilon : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  epsilon * p 0 * directedWeight b lambda I p

def weightH0 (b lambda : ℝ) (p : Coord) : ℝ := lambda + 8 / edgeDistance b p

variable {I : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem directedWeight_differentiableAt
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    DifferentiableAt ℝ (directedWeight b lambda I) p := by
  have hD := (hasFDerivAt_const (𝕜 := ℝ) b p).sub (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hPhi := ((hasFDerivAt_apply (𝕜 := ℝ) 1 p).const_mul (-lambda)).add hI.hasFDerivAt
  have hd := (hD.pow 8).fun_mul hPhi.exp
  simp only [Pi.add_def, Pi.sub_def] at hd
  exact hd.differentiableAt

theorem directedWeight_contDiffOn (b lambda : ℝ) (hI : ContDiffOn ℝ ∞ I U) :
    ContDiffOn ℝ ∞ (directedWeight b lambda I) U := by
  have hy : ContDiffOn ℝ ∞ (fun p : Coord => p 1) U :=
    contDiffOn_apply ℝ ℝ 1 U
  have hD : ContDiffOn ℝ ∞ (fun p : Coord => b - p 1) U :=
    contDiffOn_const.sub hy
  have hLambda : ContDiffOn ℝ ∞ (fun _ : Coord => -lambda) U := contDiffOn_const
  have hPhi : ContDiffOn ℝ ∞ (fun p : Coord => -lambda * p 1 + I p) U :=
    (hLambda.mul hy).add hI
  exact (hD.pow 8).mul hPhi.exp

theorem directedWeight_pos (b lambda : ℝ) (I : Coord → ℝ) (p : Coord) (hp : p 1 < b) :
    0 < directedWeight b lambda I p :=
  mul_pos (pow_pos (sub_pos.mpr hp) 8) (Real.exp_pos _)

theorem directedWeight_edge_zero (b lambda : ℝ) (I : Coord → ℝ) (p : Coord)
    (hp : p 1 = b) : directedWeight b lambda I p = 0 := by
  simp [directedWeight, edgeDistance, hp]

theorem directedM_differentiableAt
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    DifferentiableAt ℝ (directedM b lambda I) p :=
  (directedWeight_differentiableAt b lambda hI).neg

theorem directedN_differentiableAt
    (b lambda epsilon : ℝ) (hI : DifferentiableAt ℝ I p) :
    DifferentiableAt ℝ (directedN b lambda epsilon I) p :=
  ((differentiableAt_apply (𝕜 := ℝ) 0 p).const_mul epsilon).mul
    (directedWeight_differentiableAt b lambda hI)

theorem directed_mn_edge_zero
    (b lambda epsilon : ℝ) (I : Coord → ℝ) (p : Coord) (hp : p 1 = b) :
    directedM b lambda I p = 0 ∧ directedN b lambda epsilon I p = 0 := by
  simp [directedM, directedN, directedWeight_edge_zero b lambda I p hp]

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_WeightPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry SmoothLocal.ODE

variable {B : Coord → ℝ} {R a b : ℝ}

theorem compact_t_mem_rectangle_interval {r : ℝ} (hrR : r < R) (x : Icc (-r) r) :
    (x : ℝ) ∈ Ioo (-R) R :=
  ⟨(neg_lt_neg hrR).trans_le x.2.1, x.2.2.trans_lt hrR⟩

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

theorem normalized_loss_budget {H A MA L mu : ℝ}
    (hH : 0 < H) (hL : 0 ≤ L) (hA : |A| ≤ MA)
    (hsmall : L * MA ≤ 1 / 8) (hloss : L / H ≤ mu / 4) :
    L * (H⁻¹ + H * A ^ 2) ≤ mu / 4 + H * |A| / 8 := by
  have hLA : L * |A| ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left hA hL).trans hsmall
  have hLA2 : L * A ^ 2 ≤ |A| / 8 := by
    have hm := mul_le_mul_of_nonneg_right hLA (abs_nonneg A)
    nlinarith [sq_abs A]
  have hmul := mul_le_mul_of_nonneg_left hLA2 hH.le
  calc
    _ = L / H + H * (L * A ^ 2) := by ring
    _ ≤ mu / 4 + H * (|A| / 8) := add_le_add hloss hmul
    _ = _ := by ring

theorem residual_abs_error_bound {A e E H : ℝ}
    (he : |e| ≤ E) (hEH : E ≤ H / 8) :
    -(H * |A| / 8) ≤ A * e := by
  have habs : |A * e| ≤ H * |A| / 8 := by
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_left (he.trans hEH) (abs_nonneg A)
    nlinarith only [h]
  exact (abs_le.mp habs).1

theorem normalized_negative_near_coercivity {H A MA L mu Q e E : ℝ}
    (hH : 0 < H) (hL : 0 ≤ L) (hmu : 0 < mu) (hA : A ≤ 0) (hAM : |A| ≤ MA)
    (hsmall : L * MA ≤ 1 / 8) (hloss : L / H ≤ mu / 4)
    (he : |e| ≤ E) (hEH : E ≤ H / 8) (hQ : mu ≤ Q) :
    mu / 2 + H * |A| / 4 ≤ Q - H * A / 2 + A * e - L * (H⁻¹ + H * A ^ 2) := by
  have hcross := normalized_loss_budget hH hL hAM hsmall hloss
  have herr := residual_abs_error_bound (A := A) he hEH
  rw [abs_of_nonpos hA] at *
  nlinarith

theorem normalized_positive_strip_coercivity {H A MA L mu Q e E : ℝ}
    (hH : 0 < H) (hL : 0 ≤ L) (_ : 0 < mu) (hA : 0 ≤ A) (hAM : |A| ≤ MA)
    (hsmall : L * MA ≤ 1 / 8) (hloss : L / H ≤ mu / 4)
    (he : |e| ≤ E) (hEH : E ≤ H / 8) (hQ : mu ≤ Q) (hstrip : H * A ≤ mu / 3) :
    mu / 2 ≤ Q - H * A / 2 + A * e - L * (H⁻¹ + H * A ^ 2) := by
  have hcross := normalized_loss_budget hH hL hAM hsmall hloss
  have herr := residual_abs_error_bound (A := A) he hEH
  rw [abs_of_nonneg hA] at *
  nlinarith

theorem normalized_negative_far_coercivity {H A MA L mu Q e E alpha Pmax : ℝ}
    (hH : 0 < H) (hL : 0 ≤ L) (hmu : 0 < mu) (hA : A ≤ 0) (hAM : |A| ≤ MA)
    (hsmall : L * MA ≤ 1 / 8) (hloss : L / H ≤ mu / 4)
    (he : |e| ≤ E) (hEH : E ≤ H / 8) (hQ : -Pmax ≤ Q)
    (halpha : alpha ≤ |A|) (hbudget : Pmax + mu ≤ H * alpha / 4) :
    mu / 2 ≤ Q - H * A / 2 + A * e - L * (H⁻¹ + H * A ^ 2) := by
  have hcross := normalized_loss_budget hH hL hAM hsmall hloss
  have herr := residual_abs_error_bound (A := A) he hEH
  have hmargin : Pmax + mu ≤ H * |A| / 4 := by
    have hm := mul_le_mul_of_nonneg_left halpha hH.le
    nlinarith
  rw [abs_of_nonpos hA] at *
  nlinarith

theorem actual_quadratic_coercivity {T S J W H lambda mu Q e A L x y : ℝ}
    (hW : 0 < W) (hH : 0 < H) (_ : 0 < lambda) (_ : 0 < mu)
    (hlH : lambda ≤ H) (hT : W * H / 4 ≤ T)
    (hS : S = W * (Q - H * A / 2 + A * e))
    (hcross : J ^ 2 / (2 * T * W) ≤ L * (H⁻¹ + H * A ^ 2))
    (hmargin : mu / 2 ≤ Q - H * A / 2 + A * e - L * (H⁻¹ + H * A ^ 2)) :
    min (lambda / 8) (mu / 2) * W * (x ^ 2 + y ^ 2) ≤ T * x ^ 2 + S * y ^ 2 + J * x * y := by
  have hTpos : 0 < T := (show 0 < W * H / 4 by positivity).trans_le hT
  have hcross' : J ^ 2 / (2 * T) ≤ W * (L * (H⁻¹ + H * A ^ 2)) := by
    have hm := mul_le_mul_of_nonneg_right hcross hW.le
    have he : J ^ 2 / (2 * T * W) * W = J ^ 2 / (2 * T) := by
      field_simp [hTpos.ne', hW.ne']
    rw [he] at hm
    nlinarith only [hm]
  have hSlo : mu / 2 * W ≤ S - J ^ 2 / (2 * T) := by
    have hm := mul_le_mul_of_nonneg_left hmargin hW.le
    rw [hS]
    nlinarith only [hm, hcross']
  have hTlo : lambda / 8 * W ≤ T / 2 := by
    have hm := mul_le_mul_of_nonneg_left hlH hW.le
    nlinarith only [hm, hT]
  have hxlo : min (lambda / 8) (mu / 2) * W ≤ T / 2 :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hW.le).trans hTlo
  have hylo : min (lambda / 8) (mu / 2) * W ≤ S - J ^ 2 / (2 * T) :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hW.le).trans hSlo
  have hx := mul_le_mul_of_nonneg_right hxlo (sq_nonneg x)
  have hy := mul_le_mul_of_nonneg_right hylo (sq_nonneg y)
  have hq := quadratic_cross_absorption (S := S) (J := J) (u := x) (v := y) hTpos
  nlinarith only [hx, hy, hq]

theorem actual_normalized_cross_loss {T J W H A Cj epsilon : ℝ}
    (hW : 0 < W) (hH : 0 < H) (hCj : 0 ≤ Cj) (heps : 0 ≤ epsilon)
    (hT : W * H / 4 ≤ T)
    (hJ : |J| ≤ W * Cj * epsilon * (1 + H * |A|)) :
    J ^ 2 / (2 * T * W) ≤ 4 * Cj ^ 2 * epsilon ^ 2 * (H⁻¹ + H * A ^ 2) := by
  have hh := cross_loss_bound hW hH hCj heps hT hJ
  have hTpos : 0 < T := (show 0 < W * H / 4 by positivity).trans_le hT
  have he : J ^ 2 / (2 * T * W) = (J ^ 2 / (T * W)) / 2 := by
    field_simp [hTpos.ne', hW.ne']
  rw [he]
  nlinarith only [hh]

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_ModelCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Model

open SmoothLocal.Geometry SmoothLocal.Weighted

theorem squareTransition_deriv_zero_left {t : ℝ} (ht : t ≤ 1 / 4) :
    deriv squareTransition t = 0 := by
  have hmin : IsLocalMin squareTransition t := Filter.Eventually.of_forall (fun x => by
    rw [squareTransition_zero ht]
    exact (squareTransition_range x).1)
  exact hmin.deriv_eq_zero

theorem squareTransition_deriv_zero_right {t : ℝ} (ht : 1 / 2 ≤ t) :
    deriv squareTransition t = 0 := by
  have hmax : IsLocalMax squareTransition t := Filter.Eventually.of_forall (fun x => by
    rw [squareTransition_one ht]
    exact (squareTransition_range x).2)
  exact hmax.deriv_eq_zero

theorem modelProfile_deriv_outer {y : ℝ} (hy : 1 / 2 ≤ y ^ 2) :
    deriv modelProfile y = -2 * y := by
  rw [modelProfile_deriv, squareTransition_one hy, squareTransition_deriv_zero_right hy]
  ring

theorem modelProfile_deriv_nonneg_lower_cap {y : ℝ} (hy : y ≤ 1 / 50) :
    0 ≤ deriv modelProfile y := by
  by_cases hy0 : y ≤ 0
  · rw [modelProfile_deriv]
    have hy3 : y ^ 3 ≤ 0 := by
      have hh := mul_nonpos_of_nonpos_of_nonneg hy0 (sq_nonneg y)
      nlinarith only [hh]
    have hfirst : 0 ≤ -2 * y * squareTransition (y ^ 2) :=
      mul_nonneg (by linarith) (squareTransition_range _).1
    have hsecond : 0 ≤ -2 * y ^ 3 * deriv squareTransition (y ^ 2) :=
      mul_nonneg (by linarith) (squareTransition_deriv_nonneg _)
    linarith
  · have hypos : 0 < y := lt_of_not_ge hy0
    have hysq : y ^ 2 ≤ 1 / 4 :=
      (pow_le_pow_left₀ hypos.le hy 2).trans (by norm_num)
    rw [modelProfile_deriv, squareTransition_zero hysq, squareTransition_deriv_zero_left hysq]
    norm_num

theorem modelProfile_deriv_lower_three_quarters {y : ℝ} (hy : y ≤ -(3 / 4 : ℝ)) :
    3 / 2 ≤ deriv modelProfile y := by
  have hs : (3 / 4 : ℝ) ^ 2 ≤ (-y) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith : (3 / 4 : ℝ) ≤ -y) 2
  have hysq : 1 / 2 ≤ y ^ 2 := by nlinarith only [hs]
  rw [modelProfile_deriv_outer hysq]
  linarith

theorem modelProfile_middle_lower {y : ℝ}
    (hylo : -(3 / 4 : ℝ) ≤ y) (hyhi : y ≤ 1 / 50) :
    7 / 16 ≤ modelProfile y := by
  have hy2 : y ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := sq_le_sq' hylo (by linarith)
  nlinarith [(modelProfile_bounds y).1]

theorem modelCurvature_middle_xsq_lower {kappa : ℝ} (hkappa : 0 < kappa)
    {p : Coord} (hylo : -(3 / 4 : ℝ) ≤ p 1) (hyhi : p 1 ≤ 1 / 50)
    (hK : |modelCurvature kappa p| ≤ kappa / 8) :
    5 / 16 ≤ (p 0) ^ 2 := by
  have hh := mul_le_mul_of_nonneg_left (modelProfile_middle_lower hylo hyhi) hkappa.le
  have hlower := (abs_le.mp hK).1
  unfold modelCurvature at hlower
  have hprod : kappa * (5 / 16) ≤ kappa * (p 0) ^ 2 := by nlinarith only [hh, hlower]
  exact le_of_mul_le_mul_left hprod hkappa

theorem directed_model_slope_lower {rho rhoMax epsilon R Mq t q : ℝ} (ell : ℕ)
    (hrho : 0 < rho) (hrhoMax : rho ≤ rhoMax) (heps : 0 ≤ epsilon)
    (ht : |t| ≤ R) (hq : |q| ≤ Mq)
    (hsmall : epsilon * R * Mq ≤ ((ell : ℝ) + 1 / 2) / rhoMax) :
    ((ell : ℝ) + 1 / 2) / (2 * rhoMax) ≤
      ((ell : ℝ) + 1 / 2) / rho + epsilon * t * q / 2 := by
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have hMq : 0 ≤ Mq := (abs_nonneg _).trans hq
  have hmax : 0 < rhoMax := hrho.trans_le hrhoMax
  have hbeta : 0 ≤ (ell : ℝ) + 1 / 2 := by positivity
  have hfrac : ((ell : ℝ) + 1 / 2) / rhoMax ≤ ((ell : ℝ) + 1 / 2) / rho :=
    (div_le_div_iff₀ hmax hrho).2 (mul_le_mul_of_nonneg_left hrhoMax hbeta)
  have hprod : |epsilon * t * q| ≤ epsilon * R * Mq := by
    rw [abs_mul, abs_mul, abs_of_nonneg heps]
    exact mul_le_mul (mul_le_mul_of_nonneg_left ht heps) hq
      (abs_nonneg _) (mul_nonneg heps hR)
  have hprodlo := (abs_le.mp (hprod.trans hsmall)).1
  have he : ((ell : ℝ) + 1 / 2) / (2 * rhoMax) =
      (((ell : ℝ) + 1 / 2) / rhoMax) / 2 := by ring
  rw [he]
  linarith

end SmoothLocal.Model

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MultiplierIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

variable {tl tr sb st : ℝ} {f g : Coord → ℝ}

variable {U : Set Coord}

def cutoffM (chi : Coord → ℝ) (edge lambda : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  chi p * directedM edge lambda I p

def cutoffN (chi : Coord → ℝ) (edge lambda epsilon : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  chi p * directedN edge lambda epsilon I p

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_PicardFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric Function
open scoped Topology NNReal ContDiff

namespace SmoothLocal.Flow

theorem exists_confined_continuous_picard_family
    {f : ℝ → ℝ → ℝ} {tmin tmax : ℝ} {t0 : Icc tmin tmax} {x0 : ℝ}
    {a r L K : ℝ≥0} (hf : IsPicardLindelof f t0 x0 a r L K) :
    ∃ Y : ℝ → ℝ → ℝ,
      (∀ s ∈ closedBall x0 r, Y s t0 = s ∧
        ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (Y s) (f t (Y s t)) (Icc tmin tmax) t) ∧
      (∀ s ∈ closedBall x0 r, ∀ t, Y s t ∈ closedBall x0 a) ∧
      (∃ J : ℝ≥0, ∀ t, LipschitzOnWith J (fun s => Y s t) (closedBall x0 r)) ∧
      ContinuousOn (uncurry Y) (closedBall x0 r ×ˢ Icc tmin tmax) ∧
      (∀ s ∈ closedBall x0 r, LipschitzOnWith L (Y s) (Icc tmin tmax)) := by
  classical
  have hex (s : ℝ) (hs : s ∈ closedBall x0 r) :=
    ODE.FunSpace.exists_isFixedPt_next hf hs
  choose alpha halpha using hex
  let Y : ℝ → ℝ → ℝ := fun s => if hs : s ∈ closedBall x0 r then
    (alpha s hs).compProj else fun _ => 0
  have hY (s : ℝ) (hs : s ∈ closedBall x0 r) : Y s = (alpha s hs).compProj := by
    simp only [Y, dite_eq_left hs]
  have hstart (s : ℝ) (hs : s ∈ closedBall x0 r) : Y s t0 = s := by
    rw [hY s hs, ODE.FunSpace.compProj_val, ← halpha s hs,
      ODE.FunSpace.next_apply₀]
  have hderiv (s : ℝ) (hs : s ∈ closedBall x0 r) (t : ℝ)
      (ht : t ∈ Icc tmin tmax) :
      HasDerivWithinAt (Y s) (f t (Y s t)) (Icc tmin tmax) t := by
    rw [hY s hs]
    apply ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
      (alpha s hs).continuous_compProj.continuousOn
      (fun _ _ => (alpha s hs).compProj_mem_closedBall hf.mul_max_le) s ht
      |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← halpha s hs]
    rw [ODE.FunSpace.compProj_of_mem ht']
    exact ODE.FunSpace.next_apply hf hs (alpha s hs)
  have hrange (s : ℝ) (hs : s ∈ closedBall x0 r) (t : ℝ) :
      Y s t ∈ closedBall x0 a := by
    rw [hY s hs]
    exact (alpha s hs).compProj_mem_closedBall hf.mul_max_le
  obtain ⟨J, hJ⟩ := ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
  have hinitLip (t : ℝ) : LipschitzOnWith J (fun s => Y s t) (closedBall x0 r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs u hu
    rw [hY s hs, hY u hu, ODE.FunSpace.compProj_apply, ODE.FunSpace.compProj_apply,
      ← ODE.FunSpace.toContinuousMap_apply_eq_apply,
      ← ODE.FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t0⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact hJ s u hs hu (alpha s hs) (alpha u hu) (halpha s hs) (halpha u hu)
  have hcont : ContinuousOn (uncurry Y) (closedBall x0 r ×ˢ Icc tmin tmax) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ J
    · intro s hs
      exact HasDerivWithinAt.continuousOn (hderiv s hs)
    · intro t _
      exact hinitLip t
  have htimeLip (s : ℝ) (hs : s ∈ closedBall x0 r) :
      LipschitzOnWith L (Y s) (Icc tmin tmax) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht u hu
    rw [hY s hs, ODE.FunSpace.compProj_of_mem ht, ODE.FunSpace.compProj_of_mem hu]
    exact (alpha s hs).lipschitzWith.dist_le_mul ⟨t, ht⟩ ⟨u, hu⟩
  exact ⟨Y, fun s hs => ⟨hstart s hs, hderiv s hs⟩, hrange, ⟨J, hinitLip⟩, hcont, htimeLip⟩

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_ChainTermDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation

theorem iteratedDeriv_contDiffAt_infty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : ℝ → E} {t : ℝ} (hJ : ContDiffAt ℝ ∞ J t) :
    ∀ n, ContDiffAt ℝ ∞ (iteratedDeriv n J) t := by
  intro n
  induction n with
  | zero => simpa using hJ
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact hn.derivWithin (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

theorem iteratedDeriv_hasDerivAt_infty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : ℝ → E} {t : ℝ} (hJ : ContDiffAt ℝ ∞ J t) (n : ℕ) :
    HasDerivAt (iteratedDeriv n J) (iteratedDeriv (n + 1) J t) t := by
  rw [iteratedDeriv_succ]
  exact ((iteratedDeriv_contDiffAt_infty hJ n).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_ScalarChainExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def stateBaseOrder : Fin 6 → ℕ := ![0, 0, 1, 1, 2, 2]

theorem stateBaseOrder_le_two (i : Fin 6) : stateBaseOrder i ≤ 2 := by
  fin_cases i <;> (first | (simp [stateBaseOrder]; all_goals first | (norm_num [stateBaseOrder]; done) | rfl | decide) | (norm_num [stateBaseOrder]; done) | norm_num [stateBaseOrder])

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_MixedCoordinateCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem coordinateDirections_apply (ds : List (Fin 2)) (i : Fin ds.length) :
    coordinateDirections ds i = Pi.single (ds.get i) (1 : ℝ) := by
  induction ds with
  | nil => exact Fin.elim0 i
  | cons a ds ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih j

theorem fullJet_linear_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Coord →L[ℝ] E) {n : ℕ} (hn : 2 ≤ n) (p : Coord) (v : Fin n → Coord) :
    iteratedFDeriv ℝ n L p v = 0 := by
  cases n with
  | zero => omega
  | succ n =>
      have hn0 : n ≠ 0 := by omega
      rw [iteratedFDeriv_succ_apply_right]
      have he : (fun q => fderiv ℝ L q) = fun _ : Coord => L := by
        funext q
        exact L.fderiv
      rw [he, iteratedFDeriv_const_of_ne hn0]
      simp

theorem word_two_x_permutation (ds : List (Fin 2)) (hx : 2 ≤ ds.count 0) :
    ∃ es : List (Fin 2), ds.Perm (es ++ [0, 0]) := by
  have h0 : (0 : Fin 2) ∈ ds := List.count_pos_iff.mp (by omega)
  have h1 : (0 : Fin 2) ∈ ds.erase 0 := List.count_pos_iff.mp (by
    rw [List.count_erase_self]
    omega)
  refine ⟨(ds.erase 0).erase 0, ?_⟩
  have h := (List.perm_cons_erase h0).trans ((List.perm_cons_erase h1).cons 0)
  exact h.trans (show ([0, 0] ++ (ds.erase 0).erase 0).Perm
    ((ds.erase 0).erase 0 ++ [0, 0]) from List.perm_append_comm)

theorem mixed_principal_word_orders (es : List (Fin 2)) :
    (es ++ [0, 1]).length = (es ++ [0, 0]).length ∧
    (es ++ [1, 1]).length = (es ++ [0, 0]).length ∧
    (es ++ [0, 1]).count 0 < (es ++ [0, 0]).count 0 ∧
    (es ++ [1, 1]).count 0 < (es ++ [0, 0]).count 0 := by
  simp

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_CoordinateJetReverseNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace SmoothLocal.Geometry
open SmoothLocal.HighEquation

theorem coordinate_basis_decomposition (v : Coord) :
    v = ∑ i : Fin 2, v i • (Pi.single i (1 : ℝ) : Coord) := by
  ext j
  simp [Pi.single_apply, Finset.sum_apply, smul_eq_mul]

theorem multilinear_coordinate_components {n : ℕ}
    (L : Coord [×n]→L[ℝ] ℝ) (v : Fin n → Coord) :
    L v = ∑ r : Fin n → Fin 2,
      L (fun i => Pi.single (r i) (1 : ℝ)) * ∏ i, v i (r i) := by
  classical
  calc
    L v = L (fun i => ∑ j : Fin 2, v i j • (Pi.single j (1 : ℝ) : Coord)) := by
      congr 1
      funext i
      exact coordinate_basis_decomposition (v i)
    _ = ∑ r : Fin n → Fin 2, L (fun i => v i (r i) • Pi.single (r i) (1 : ℝ)) :=
      L.map_sum (fun i j => v i j • (Pi.single j (1 : ℝ) : Coord))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [L.map_smul_univ]
      simp only [smul_eq_mul, mul_comm]

theorem multilinear_norm_le_coordinate_bound {n : ℕ}
    (L : Coord [×n]→L[ℝ] ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hL : ∀ r : Fin n → Fin 2, ‖L (fun i => Pi.single (r i) (1 : ℝ))‖ ≤ B) :
    ‖L‖ ≤ (2 : ℝ)^n * B := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) hB)
  intro v
  rw [multilinear_coordinate_components]
  calc
    _ ≤ ∑ r : Fin n → Fin 2, ‖L (fun i => Pi.single (r i) (1 : ℝ)) * ∏ i, v i (r i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r : Fin n → Fin 2, B * ∏ i, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul, norm_prod]
      apply mul_le_mul (hL r) _ (by positivity) hB
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun i _ => norm_le_pi_norm (v i) (r i))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

end SmoothLocal.Geometry

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

variable {P S bTheta bXi v R : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem scalar_flux_bound (P S a b : ℝ) (hS : 0 ≤ S) :
    |P * a ^ 2 / 2 + S * b * a| ≤
      (|P| + Real.sqrt S) * ((a ^ 2 + S * b ^ 2) / 2) := by
  have hs := Real.sqrt_nonneg S
  have hs2 := Real.sq_sqrt hS
  have hab : 2 * Real.sqrt S * (|a| * |b|) ≤ a ^ 2 + S * b ^ 2 := by
    nlinarith [sq_nonneg (|a| - Real.sqrt S * |b|), sq_abs a, sq_abs b]
  have hab' := mul_le_mul_of_nonneg_left hab hs
  have hsimpl : Real.sqrt S * (2 * Real.sqrt S * (|a| * |b|)) =
      2 * S * |b| * |a| := by
    calc
      _ = 2 * (Real.sqrt S) ^ 2 * |b| * |a| := by ring
      _ = _ := by rw [hs2]
  rw [hsimpl] at hab'
  have hsa : S * |b| * |a| ≤ Real.sqrt S * ((a ^ 2 + S * b ^ 2) / 2) := by
    nlinarith only [hab']
  calc
    _ ≤ |P * a ^ 2 / 2| + |S * b * a| := abs_add_le _ _
    _ = |P| * a ^ 2 / 2 + S * |b| * |a| := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg a),
        abs_mul, abs_mul, abs_of_nonneg hS]
      norm_num
    _ ≤ |P| * ((a ^ 2 + S * b ^ 2) / 2) +
        Real.sqrt S * ((a ^ 2 + S * b ^ 2) / 2) := by
      have hsb := mul_nonneg (abs_nonneg P) (mul_nonneg hS (sq_nonneg b))
      nlinarith
    _ = _ := by ring

theorem scalar_coefficient_error_bound
    {s0 S M bt bx Px Sx St a b : ℝ} (hs0 : 0 < s0) (hS : s0 ≤ S)
    (hM : 0 ≤ M) (hbt : |bt| ≤ M) (hbx : |bx| ≤ M)
    (hPx : |Px| ≤ M) (hSx : |Sx| ≤ M) (hSt : |St| ≤ M) :
    |(bt - Px / 2) * a ^ 2 + (bx - Sx) * b * a + St / 2 * b ^ 2| ≤
      (8 * M * (1 + 1 / s0)) * ((a ^ 2 + S * b ^ 2) / 2) := by
  have hA : |bt - Px / 2| ≤ 2 * M := by
    have hh := abs_sub bt (Px / 2)
    rw [abs_div] at hh
    norm_num at hh
    linarith
  have hB : |bx - Sx| ≤ 2 * M := (abs_sub _ _).trans (by linarith)
  have hC : |St / 2| ≤ M := by rw [abs_div]; norm_num; linarith
  have hab : |b| * |a| ≤ (a ^ 2 + b ^ 2) / 2 := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have hrough :
      |(bt - Px / 2) * a ^ 2 + (bx - Sx) * b * a + St / 2 * b ^ 2| ≤
        4 * M * (a ^ 2 + b ^ 2) := by
    calc
      _ ≤ |(bt - Px / 2) * a ^ 2| + |(bx - Sx) * b * a| + |St / 2 * b ^ 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |bt - Px / 2| * a ^ 2 + |bx - Sx| * (|b| * |a|) + |St / 2| * b ^ 2 := by
        simp only [abs_mul, abs_of_nonneg (sq_nonneg a), abs_of_nonneg (sq_nonneg b)]
        ring
      _ ≤ (2 * M) * a ^ 2 + (2 * M) * ((a ^ 2 + b ^ 2) / 2) + M * b ^ 2 := by
        gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hM (sq_nonneg a), mul_nonneg hM (sq_nonneg b)]
  have hinv : 0 < 1 / s0 := one_div_pos.mpr hs0
  have hsb : b ^ 2 ≤ (1 / s0) * (S * b ^ 2) := by
    have hh := mul_le_mul_of_nonneg_right hS (sq_nonneg b)
    have hh' : b ^ 2 ≤ (S * b ^ 2) / s0 :=
      (le_div_iff₀ hs0).2 (by nlinarith)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh'
  have hcompare : a ^ 2 + b ^ 2 ≤ (1 + 1 / s0) * (a ^ 2 + S * b ^ 2) := by
    nlinarith [mul_nonneg hinv.le (sq_nonneg a), mul_nonneg (hs0.le.trans hS) (sq_nonneg b)]
  exact hrough.trans (by nlinarith [mul_le_mul_of_nonneg_left hcompare (by positivity : 0 ≤ 4 * M)])

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

def inwardLeft (x0 theta0 speed : ℝ) (theta : ℝ) : ℝ :=
  x0 + speed * (theta - theta0)

def inwardRight (x0 theta0 speed : ℝ) (theta : ℝ) : ℝ :=
  x0 - speed * (theta - theta0)

theorem inwardLeft_hasDerivAt (x0 theta0 speed theta : ℝ) :
    HasDerivAt (inwardLeft x0 theta0 speed) speed theta := by
  unfold inwardLeft
  simpa only [inwardLeft, mul_one, id_eq] using
    (((hasDerivAt_id theta).sub_const theta0).const_mul speed).const_add x0

theorem inwardRight_hasDerivAt (x0 theta0 speed theta : ℝ) :
    HasDerivAt (inwardRight x0 theta0 speed) (-speed) theta := by
  unfold inwardRight
  simpa only [inwardRight, mul_one, zero_sub, id_eq, Pi.sub_def] using
    (hasDerivAt_const theta x0).sub
      (((hasDerivAt_id theta).sub_const theta0).const_mul speed)

end SmoothLocal.Hyperbolic

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

section SmoothLowerJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S : Set E} {G : E → MetricMatrix} {D : E → MetricFirstJet}

theorem metricMatrix_inverse_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun s => (G s)⁻¹ i j) S := by
  have hd : ContDiffOn ℝ ∞ (fun s => (G s).det) S := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  have ha : ContDiffOn ℝ ∞ (fun s => (G s).adjugate i j) S := by
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_two] using hG 1 1
    · simpa [Matrix.adjugate_fin_two] using (hG 0 1).neg
    · simpa [Matrix.adjugate_fin_two] using (hG 1 0).neg
    · simpa [Matrix.adjugate_fin_two] using hG 0 0
  simpa [Matrix.inv_def,Ring.inverse_eq_inv,smul_eq_mul] using (hd.inv hdet).mul ha

theorem christoffelJet_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hD : ∀ d i j, ContDiffOn ℝ ∞ (fun s => D s d i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) (k i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun s => christoffelJet (G s) (D s) k i j) S := by
  have hi := metricMatrix_inverse_contDiffOn hG hdet
  have ht (l : Fin 2) : ContDiffOn ℝ ∞
      (fun s => (G s)⁻¹ k l * (D s i j l+D s j i l-D s l i j)) S :=
    (hi k l).mul (((hD i j l).add (hD j i l)).sub (hD l i j))
  simpa only [christoffelJet,Fin.sum_univ_two] using
    (contDiffOn_const (c := (1/2 : ℝ))).mul ((ht 0).add (ht 1))

end SmoothLowerJet

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseProfiles
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

def axisBump (a t : ℝ) : ℝ := expNegInvGlue (a ^ 2 - t ^ 2)

theorem axisBump_contDiff (a : ℝ) : ContDiff ℝ ∞ (axisBump a) :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

theorem axisBump_nonneg (a t : ℝ) : 0 ≤ axisBump a t := expNegInvGlue.nonneg _

theorem axisBump_zero {a t : ℝ} (ha : 0 ≤ a) (ht : a ≤ |t|) : axisBump a t = 0 := by
  have hs : a ^ 2 ≤ |t| ^ 2 := (sq_le_sq₀ ha (abs_nonneg t)).mpr ht
  exact expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (by simpa only [sq_abs] using hs))

theorem axisBump_support_bound {a t : ℝ} (ha : 0 < a) (ht : axisBump a t ≠ 0) :
    |t| < a := by
  by_contra h
  exact ht (axisBump_zero ha.le (le_of_not_gt h))

theorem axisBump_tsupport_subset {a : ℝ} (ha : 0 < a) :
    tsupport (axisBump a) ⊆ Icc (-a) a := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  exact ⟨(abs_lt.mp (axisBump_support_bound ha ht)).1.le,
    (abs_lt.mp (axisBump_support_bound ha ht)).2.le⟩

theorem axisBump_hasCompactSupport {a : ℝ} (ha : 0 < a) : HasCompactSupport (axisBump a) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (axisBump_tsupport_subset ha)

def temporalCutoff : ℝ → ℝ := axisBump (1 / 2)

def inverseShearMatrix (q0 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; -q0, 1]

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

@[simp] theorem inverseShearMatrix_det (q0 : ℝ) : (inverseShearMatrix q0).det = 1 := by
  simp [inverseShearMatrix,Matrix.det_fin_two]

theorem inverseShearMatrix_isUnit (q0 : ℝ) : IsUnit (inverseShearMatrix q0) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  simp

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_ShearSpeedBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SmoothLocal.Pulse

theorem shear_time_factor_bound {v b a : ℝ} (hv : 0 < v)
    (hb : |b| ≤ v / 2) (ha : a ≤ -(v ^ 2)) :
    v ^ 2 / 2 ≤ -(b ^ 2 + a) := by
  have hb2 : b ^ 2 ≤ (v / 2) ^ 2 := by
    have ht := (sq_le_sq₀ (abs_nonneg b) (by positivity : 0 ≤ v / 2)).mpr hb
    simpa only [sq_abs] using ht
  nlinarith [sq_nonneg v]

theorem shear_principal_speed {v b a : ℝ} (hv : 0 < v)
    (hb : |b| ≤ v / 2) (ha : a ≤ -(v ^ 2)) :
    0 < -1 / (b ^ 2 + a) ∧
      |2 * b / (b ^ 2 + a)| + Real.sqrt (-1 / (b ^ 2 + a)) ≤ 4 / v := by
  let d := -(b ^ 2 + a)
  have hd0 : v ^ 2 / 2 ≤ d := shear_time_factor_bound hv hb ha
  have hv2 : 0 < v ^ 2 := sq_pos_of_pos hv
  have hd : 0 < d := (half_pos hv2).trans_le hd0
  have hS : -1 / (b ^ 2 + a) = 1 / d := by
    dsimp only [d]
    rw [div_neg, neg_div]
  have hP : |2 * b / (b ^ 2 + a)| = 2 * |b| / d := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_neg (show b ^ 2 + a < 0 from neg_pos.mp hd)]
  have hp : 2 * |b| / d ≤ 2 / v := by
    apply (div_le_div_iff₀ hd hv).mpr
    have hh := mul_le_mul_of_nonneg_right hb hv.le
    nlinarith
  have hs : 1 / d ≤ (2 / v) ^ 2 := by
    rw [div_pow]
    apply (div_le_div_iff₀ hd hv2).mpr
    nlinarith
  have hsqrt : Real.sqrt (1 / d) ≤ 2 / v :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, hs⟩
  rw [hS, hP]
  refine ⟨one_div_pos.mpr hd, ?_⟩
  calc
    _ ≤ 2 / v + 2 / v := add_le_add hp hsqrt
    _ = 4 / v := by ring

theorem shear_width_smallness {v b : ℝ} (hv : 0 < v)
    (hb : |b| ≤ 1 / (10 * (100 * (1 + v⁻¹)))) :
    |b| ≤ v / 2 ∧ 4 / v < (100 * (1 + v⁻¹)) / 4 := by
  have hwidth : 0 < 100 * (1 + v⁻¹) := by positivity
  have hsmall : 1 / (10 * (100 * (1 + v⁻¹))) ≤ v / 1000 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hwidth)).mpr
    have he : v / 1000 * (10 * (100 * (1 + v⁻¹))) = v + 1 := by
      field_simp [hv.ne']
      ring
    rw [he]
    linarith
  refine ⟨(hb.trans hsmall).trans (by linarith), ?_⟩
  apply (div_lt_iff₀ hv).mpr
  have he : (100 * (1 + v⁻¹)) / 4 * v = 25 * (v + 1) := by
    field_simp [hv.ne']
    ring
  rw [he]
  linarith

theorem negative_curvature_factor {K E h kappa e M v : ℝ}
    (hkappa : 0 < kappa) (he : 0 < e) (hh : h ≠ 0)
    (hK : K ≤ -kappa / 2) (hE : e ≤ E) (hH : |h| ≤ M)
    (hv : v ^ 2 ≤ kappa * e / (2 * M ^ 2)) :
    K * (E / h ^ 2) ≤ -(v ^ 2) := by
  have hE0 : 0 < E := he.trans_le hE
  have hK0 : 0 < -K := by linarith
  have hM0 : 0 < M := (abs_pos.mpr hh).trans_le hH
  have hden : h ^ 2 ≤ M ^ 2 := by
    have ht := (sq_le_sq₀ (abs_nonneg h) hM0.le).mpr hH
    simpa only [sq_abs] using ht
  have hnum : kappa * e / 2 ≤ -K * E := by
    have ht := mul_le_mul (show kappa / 2 ≤ -K by linarith) hE he.le hK0.le
    nlinarith
  have hdiv : (kappa * e / 2) / M ^ 2 ≤ (-K * E) / h ^ 2 :=
    div_le_div₀ (mul_nonneg hK0.le hE0.le) hnum (sq_pos_of_ne_zero hh) hden
  have heq : kappa * e / (2 * M ^ 2) = (kappa * e / 2) / M ^ 2 := by ring
  rw [heq] at hv
  have ht := hv.trans hdiv
  have heq2 : K * (E / h ^ 2) = -((-K * E) / h ^ 2) := by ring
  rw [heq2]
  linarith

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

def shearedMetricCoordinateBudget (G q0 : ℝ) (N : ℕ) : ℝ :=
  4 * (1 + |q0|)^2 * (2 * (1 + |q0|))^N * G

theorem shearedMetricCoordinateBudget_nonneg {G : ℝ} (q0 : ℝ) (N : ℕ) (hG : 0 ≤ G) :
    0 ≤ shearedMetricCoordinateBudget G q0 N := by
  unfold shearedMetricCoordinateBudget
  positivity

theorem inverseShearMatrix_entry_bound (q0 : ℝ) (i j : Fin 2) :
    |inverseShearMatrix q0 i j| ≤ 1 + |q0| := by
  fin_cases i <;> fin_cases j <;> simp [inverseShearMatrix]
  positivity

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_SmoothMetricJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

section Smoothness
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] {t : T}
variable {G : T → MetricMatrix} {D : T → MetricFirstJet} {DD : T → MetricSecondJet}

theorem metricMatrix_inverse_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t) (hdet : (G t).det ≠ 0)
    (i j : Fin 2) : ContDiffAt ℝ ∞ (fun s => (G s)⁻¹ i j) t := by
  have hdetc : ContDiffAt ℝ ∞ (fun s => (G s).det) t := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  have hi := hdetc.inv hdet
  have ha : ContDiffAt ℝ ∞ (fun s => (G s).adjugate i j) t := by
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_two] using hG 1 1
    · convert (hG 0 1).neg using 1
      all_goals try with_reducible_and_instances rfl
      funext s
      simp [Matrix.adjugate_fin_two]
    · convert (hG 1 0).neg using 1
      all_goals try with_reducible_and_instances rfl
      funext s
      simp [Matrix.adjugate_fin_two]
    · simpa [Matrix.adjugate_fin_two] using hG 0 0
  have hh : ContDiffAt ℝ ∞ (fun s => (G s).det⁻¹ * (G s).adjugate i j) t := hi.mul ha
  simpa [Matrix.inv_def, Ring.inverse_eq_inv, smul_eq_mul] using hh

theorem inverseDerivativeJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hdet : (G t).det ≠ 0) (d i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun s => inverseDerivativeJet (G s) (D s) d i j) t := by
  have hi := metricMatrix_inverse_contDiffAt hG hdet
  have ht (a b : Fin 2) :
      ContDiffAt ℝ ∞ (fun s => (G s)⁻¹ i a * D s d a b * (G s)⁻¹ b j) t :=
    ((hi i a).mul (hD d a b)).mul (hi b j)
  simpa only [inverseDerivativeJet, Fin.sum_univ_two] using
    (((ht 0 0).add (ht 0 1)).add ((ht 1 0).add (ht 1 1))).neg

theorem christoffelJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hdet : (G t).det ≠ 0) (k i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun s => christoffelJet (G s) (D s) k i j) t := by
  have hi := metricMatrix_inverse_contDiffAt hG hdet
  have ht (l : Fin 2) : ContDiffAt ℝ ∞
      (fun s => (G s)⁻¹ k l * (D s i j l + D s j i l - D s l i j)) t :=
    (hi k l).mul (((hD i j l).add (hD j i l)).sub (hD l i j))
  simpa only [christoffelJet, Fin.sum_univ_two] using
    (contDiffAt_const (c := (1 / 2 : ℝ))).mul ((ht 0).add (ht 1))

theorem christoffelDerivativeJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContDiffAt ℝ ∞ (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) (d k i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun s => christoffelDerivativeJet (G s) (D s) (DD s) d k i j) t := by
  have hi := metricMatrix_inverse_contDiffAt hG hdet
  have hdi := inverseDerivativeJet_contDiffAt hG hD hdet
  have ht (l : Fin 2) : ContDiffAt ℝ ∞ (fun s =>
      inverseDerivativeJet (G s) (D s) d k l * (D s i j l + D s j i l - D s l i j) +
        (G s)⁻¹ k l * (DD s d i j l + DD s d j i l - DD s d l i j)) t :=
    ((hdi d k l).mul (((hD i j l).add (hD j i l)).sub (hD l i j))).add
      ((hi k l).mul (((hDD d i j l).add (hDD d j i l)).sub (hDD d l i j)))
  simpa only [christoffelDerivativeJet, Fin.sum_univ_two] using
    (contDiffAt_const (c := (1 / 2 : ℝ))).mul ((ht 0).add (ht 1))

theorem riemannJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContDiffAt ℝ ∞ (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) (l k i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun s => riemannJet (G s) (D s) (DD s) l k i j) t := by
  have hΓ := christoffelJet_contDiffAt hG hD hdet
  have hDΓ := christoffelDerivativeJet_contDiffAt hG hD hDD hdet
  have ht (m : Fin 2) : ContDiffAt ℝ ∞ (fun s =>
      christoffelJet (G s) (D s) m j k * christoffelJet (G s) (D s) l i m -
        christoffelJet (G s) (D s) m i k * christoffelJet (G s) (D s) l j m) t :=
    ((hΓ m j k).mul (hΓ l i m)).sub ((hΓ m i k).mul (hΓ l j m))
  simpa only [riemannJet, Fin.sum_univ_two] using
    ((hDΓ i l j k).sub (hDΓ j l i k)).add ((ht 0).add (ht 1))

theorem curvatureJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContDiffAt ℝ ∞ (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun s => curvatureJet (G s) (D s) (DD s)) t := by
  have hR := riemannJet_contDiffAt hG hD hDD hdet
  have hn : ContDiffAt ℝ ∞ (fun s => ∑ l, G s 0 l * riemannJet (G s) (D s) (DD s) l 1 0 1) t := by
    simpa only [Fin.sum_univ_two] using
      ((hG 0 0).mul (hR 0 1 0 1)).add ((hG 0 1).mul (hR 1 1 0 1))
  have hd : ContDiffAt ℝ ∞ (fun s => (G s).det) t := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  exact hn.div hd hdet

end Smoothness
end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

def triangularFlow (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1, Y p.2 p.1)

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def triangularLinearEquiv (a b : ℝ) (hb : b ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun v := (v.1, a * v.1 + b * v.2)
  invFun w := (w.1, (w.2 - a * w.1) / b)
  left_inv v := by
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [hb]
      ring
  right_inv w := by
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [hb]
      ring
  map_add' v w := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add]
    ring
  map_smul' c v := by
    apply Prod.ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticAbsorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

theorem weighted_young (w x y : ℝ) (hw : 0 < w) :
    |x * y| ≤ (w * x ^ 2 + y ^ 2 / w) / 2 := by
  have hminus : 0 ≤ w * x ^ 2 - 2 * x * y + y ^ 2 / w := by
    have hn := div_nonneg (sq_nonneg (w * x - y)) hw.le
    have he : (w * x - y) ^ 2 / w = w * x ^ 2 - 2 * x * y + y ^ 2 / w := by
      field_simp [ne_of_gt hw]
      ring
    rw [he] at hn
    exact hn
  have hplus : 0 ≤ w * x ^ 2 + 2 * x * y + y ^ 2 / w := by
    have hn := div_nonneg (sq_nonneg (w * x + y)) hw.le
    have he : (w * x + y) ^ 2 / w = w * x ^ 2 + 2 * x * y + y ^ 2 / w := by
      field_simp [ne_of_gt hw]
      ring
    rw [he] at hn
    exact hn
  apply abs_le.mpr
  constructor <;> nlinarith

theorem elliptic_error_scalar_bound
    (A v u x y eT eS H : ℝ) (hv : 0 < v) (hA : 0 < A)
    (hratio : eT ^ 2 / v + eS ^ 2 / (A * v) ≤ H) :
    |u * (eT * x + eS * y)| ≤ v * (x ^ 2 + A * y ^ 2) / 2 + H * u ^ 2 / 2 := by
  have hx := weighted_young v x (u * eT) hv
  have hy := weighted_young (A * v) y (u * eS) (mul_pos hA hv)
  calc
    |u * (eT * x + eS * y)| = |x * (u * eT) + y * (u * eS)| := by congr 1; ring
    _ ≤ |x * (u * eT)| + |y * (u * eS)| := abs_add_le _ _
    _ ≤ (v * x ^ 2 + (u * eT) ^ 2 / v) / 2 +
        (A * v * y ^ 2 + (u * eS) ^ 2 / (A * v)) / 2 := add_le_add hx hy
    _ = v * (x ^ 2 + A * y ^ 2) / 2 +
        (eT ^ 2 / v + eS ^ 2 / (A * v)) * u ^ 2 / 2 := by
      field_simp [ne_of_gt hv, ne_of_gt hA]
      ring
    _ ≤ v * (x ^ 2 + A * y ^ 2) / 2 + H * u ^ 2 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hratio (sq_nonneg u)]

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def intervalCutoff (a b x : ℝ) : ℝ := Real.smoothTransition ((x - a) / (b - a))

theorem intervalCutoff_contDiff (a b : ℝ) : ContDiff ℝ ∞ (intervalCutoff a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (b - a))

theorem intervalCutoff_range (a b x : ℝ) :
    0 ≤ intervalCutoff a b x ∧ intervalCutoff a b x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem intervalCutoff_zero {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    intervalCutoff a b x = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hab).le)

theorem intervalCutoff_one {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    intervalCutoff a b x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)

theorem intervalCutoff_hasDerivAt (a b x : ℝ) :
    HasDerivAt (intervalCutoff a b)
      (deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a)) x := by
  have htheta := (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have ht : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((x - a) / (b - a))) ((x - a) / (b - a)) :=
    (htheta _).hasDerivAt
  have ha : HasDerivAt (fun y : ℝ => (y - a) / (b - a)) (1 / (b - a)) x :=
    ((hasDerivAt_id x).sub_const a).div_const (b - a)
  have hd := ht.comp x ha
  change HasDerivAt (Real.smoothTransition ∘ fun y : ℝ => (y - a) / (b - a)) _ x
  have he : deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a) =
      deriv Real.smoothTransition ((x - a) / (b - a)) * (1 / (b - a)) := by ring
  rw [he]
  exact hd

theorem intervalCutoff_deriv (a b x : ℝ) :
    deriv (intervalCutoff a b) x =
      deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a) :=
  (intervalCutoff_hasDerivAt a b x).deriv

def ellipticPhi (c x : ℝ) : ℝ := intervalCutoff (c / 2) c x

theorem ellipticPhi_contDiff (c : ℝ) : ContDiff ℝ ∞ (ellipticPhi c) :=
  intervalCutoff_contDiff _ _

theorem ellipticPhi_zero {c x : ℝ} (hc : 0 < c) (hx : x ≤ c / 2) :
    ellipticPhi c x = 0 := intervalCutoff_zero (by linarith) hx

theorem ellipticPhi_one {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    ellipticPhi c x = 1 := intervalCutoff_one (by linarith) hx

def threeEdgeCutoff (l0 l1 r1 r0 a0 a1 : ℝ) (p : Coord) : ℝ :=
  intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
    intervalCutoff a0 a1 (p 1)

theorem threeEdgeCutoff_contDiff (l0 l1 r1 r0 a0 a1 : ℝ) :
    ContDiff ℝ ∞ (threeEdgeCutoff l0 l1 r1 r0 a0 a1) := by
  exact (((intervalCutoff_contDiff l0 l1).comp (contDiff_apply ℝ ℝ 0)).mul
    ((intervalCutoff_contDiff (-r0) (-r1)).comp (contDiff_apply ℝ ℝ 0).neg)).mul
      ((intervalCutoff_contDiff a0 a1).comp (contDiff_apply ℝ ℝ 1))

theorem threeEdgeCutoff_range (l0 l1 r1 r0 a0 a1 : ℝ) (p : Coord) :
    0 ≤ threeEdgeCutoff l0 l1 r1 r0 a0 a1 p ∧
      threeEdgeCutoff l0 l1 r1 r0 a0 a1 p ≤ 1 := by
  have hL := intervalCutoff_range l0 l1 (p 0)
  have hR := intervalCutoff_range (-r0) (-r1) (-p 0)
  have hS := intervalCutoff_range a0 a1 (p 1)
  constructor
  · exact mul_nonneg (mul_nonneg hL.1 hR.1) hS.1
  · have hLR : intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) ≤ 1 := by
      nlinarith
    change intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
      intervalCutoff a0 a1 (p 1) ≤ 1
    nlinarith [mul_nonneg hL.1 hR.1]

theorem threeEdgeCutoff_one {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (p : Coord)
    (hp : l1 ≤ p 0 ∧ p 0 ≤ r1 ∧ a1 ≤ p 1) :
    threeEdgeCutoff l0 l1 r1 r0 a0 a1 p = 1 := by
  rw [threeEdgeCutoff, intervalCutoff_one hL hp.1,
    intervalCutoff_one (neg_lt_neg hR) (neg_le_neg hp.2.1),
    intervalCutoff_one hS hp.2.2]
  norm_num

theorem threeEdgeCutoff_zero {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (p : Coord)
    (hp : p 0 ≤ l0 ∨ r0 ≤ p 0 ∨ p 1 ≤ a0) :
    threeEdgeCutoff l0 l1 r1 r0 a0 a1 p = 0 := by
  rcases hp with h | h | h
  · simp [threeEdgeCutoff, intervalCutoff_zero hL h]
  · simp [threeEdgeCutoff, intervalCutoff_zero (neg_lt_neg hR) (neg_le_neg h)]
  · simp [threeEdgeCutoff, intervalCutoff_zero hS h]

theorem abs_mul_two_cutoffs_le (a b c : ℝ) (hb : 0 ≤ b ∧ b ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1) : |a * b * c| ≤ |a| := by
  rw [abs_mul, abs_mul, abs_of_nonneg hb.1, abs_of_nonneg hc.1]
  calc
    |a| * b * c ≤ |a| * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hb.2 (abs_nonneg a)) hc.2 hc.1
        (mul_nonneg (abs_nonneg a) zero_le_one)
    _ = |a| := by ring

def ellipticWeight (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) : ℝ :=
  (edgeDistance b p) ^ 6 * (chi p) ^ 2 * (ellipticPhi c (K p / edgeDistance b p)) ^ 2

def ellipticGate (b c : ℝ) (K : Coord → ℝ) (p : Coord) : ℝ :=
  ellipticPhi c (K p / edgeDistance b p)

def ellipticAmplitude (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) : ℝ :=
  (edgeDistance b p) ^ 3 * chi p * ellipticGate b c K p

theorem ellipticAmplitude_sq (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) :
    ellipticAmplitude b c chi K p ^ 2 = ellipticWeight b c chi K p := by
  unfold ellipticAmplitude ellipticGate ellipticWeight
  ring

theorem ellipticGate_differentiableAt {b c : ℝ} {K : Coord → ℝ} {p : Coord}
    (hK : DifferentiableAt ℝ K p) (hd : edgeDistance b p ≠ 0) :
    DifferentiableAt ℝ (ellipticGate b c K) p := by
  have hD : DifferentiableAt ℝ (edgeDistance b) p :=
    (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
  have hquot : DifferentiableAt ℝ (fun q => K q / edgeDistance b q) p := by
    have hm : DifferentiableAt ℝ (fun q => K q * (edgeDistance b q)⁻¹) p :=
      hK.mul (hD.inv hd)
    simpa only [div_eq_mul_inv] using hm
  exact ((ellipticPhi_contDiff c).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _).comp p hquot

theorem ellipticAmplitude_differentiableAt {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hd : edgeDistance b p ≠ 0) : DifferentiableAt ℝ (ellipticAmplitude b c chi K) p := by
  have hD : DifferentiableAt ℝ (edgeDistance b) p :=
    (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
  exact ((hD.pow 3).mul hchi).mul (ellipticGate_differentiableAt hK hd)

theorem amplitude_derivative_algebra_bound
    {d x g di xi gi X P : ℝ} (hd : 0 < d)
    (hx : 0 ≤ x ∧ x ≤ 1) (hg : 0 ≤ g ∧ g ≤ 1)
    (hdi : |di| ≤ 1) (hxi : |xi| ≤ X) (hgi : |gi| ≤ P / d) :
    |3 * d ^ 2 * di * x * g + d ^ 3 * xi * g + d ^ 3 * x * gi| ≤
      3 * d ^ 2 + d ^ 3 * X + d ^ 2 * P := by
  have hfirst : |3 * d ^ 2 * di * x * g| ≤ 3 * d ^ 2 := by
    calc
      _ ≤ |3 * d ^ 2 * di| := abs_mul_two_cutoffs_le _ _ _ hx hg
      _ = (3 * d ^ 2) * |di| := by rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (3 * d ^ 2) * 1 := mul_le_mul_of_nonneg_left hdi (by positivity)
      _ = 3 * d ^ 2 := mul_one _
  have hsecond : |d ^ 3 * xi * g| ≤ d ^ 3 * X := by
    calc
      _ = |(d ^ 3 * xi) * g * 1| := by rw [mul_one]
      _ ≤ |d ^ 3 * xi| := abs_mul_two_cutoffs_le _ _ _ hg ⟨zero_le_one, le_rfl⟩
      _ = d ^ 3 * |xi| := by rw [abs_mul, abs_of_pos (pow_pos hd _)]
      _ ≤ d ^ 3 * X := mul_le_mul_of_nonneg_left hxi (pow_pos hd _).le
  have hthird : |d ^ 3 * x * gi| ≤ d ^ 2 * P := by
    calc
      _ = |(d ^ 3 * gi) * x * 1| := by congr 1; ring
      _ ≤ |d ^ 3 * gi| := abs_mul_two_cutoffs_le _ _ _ hx ⟨zero_le_one, le_rfl⟩
      _ = d ^ 3 * |gi| := by rw [abs_mul, abs_of_pos (pow_pos hd _)]
      _ ≤ d ^ 3 * (P / d) := mul_le_mul_of_nonneg_left hgi (pow_pos hd _).le
      _ = d ^ 2 * P := by field_simp [hd.ne']
  calc
    _ ≤ |3 * d ^ 2 * di * x * g + d ^ 3 * xi * g| + |d ^ 3 * x * gi| :=
      abs_add_le _ _
    _ ≤ (|3 * d ^ 2 * di * x * g| + |d ^ 3 * xi * g|) + |d ^ 3 * x * gi| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (3 * d ^ 2 + d ^ 3 * X) + d ^ 2 * P :=
      add_le_add (add_le_add hfirst hsecond) hthird

theorem ellipticWeight_contDiffOn {chi K : Coord → ℝ} {U : Set Coord}
    (b c : ℝ) (hchi : ContDiffOn ℝ ∞ chi U) (hK : ContDiffOn ℝ ∞ K U)
    (hd : ∀ p ∈ U, p 1 < b) : ContDiffOn ℝ ∞ (ellipticWeight b c chi K) U := by
  have hD : ContDiffOn ℝ ∞ (edgeDistance b) U :=
    contDiffOn_const.sub (contDiffOn_apply ℝ ℝ 1 U)
  have hratio := hK.div hD (fun p hp => (sub_pos.mpr (hd p hp)).ne')
  exact ((hD.pow 6).mul (hchi.pow 2)).mul
    (((ellipticPhi_contDiff c).comp_contDiffOn hratio).pow 2)

theorem ellipticWeight_nonneg (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) :
    0 ≤ ellipticWeight b c chi K p := by
  unfold ellipticWeight
  positivity

theorem ellipticWeight_le_distance_six (b c : ℝ) (chi K : Coord → ℝ) (p : Coord)
    (hchi : 0 ≤ chi p ∧ chi p ≤ 1) :
    ellipticWeight b c chi K p ≤ (edgeDistance b p) ^ 6 := by
  have hphi := intervalCutoff_range (c / 2) c (K p / edgeDistance b p)
  have hc2 : (chi p) ^ 2 ≤ 1 := by nlinarith [hchi.1, hchi.2]
  have hp2 : (ellipticPhi c (K p / edgeDistance b p)) ^ 2 ≤ 1 := by
    change (intervalCutoff (c / 2) c (K p / edgeDistance b p)) ^ 2 ≤ 1
    nlinarith
  have hprod : (chi p) ^ 2 * (ellipticPhi c (K p / edgeDistance b p)) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (chi p), sq_nonneg (ellipticPhi c (K p / edgeDistance b p))]
  have hpow : 0 ≤ (edgeDistance b p) ^ 6 := by positivity
  unfold ellipticWeight
  nlinarith [mul_le_mul_of_nonneg_left hprod hpow]

theorem ellipticWeight_pos_implies_curvature {b c : ℝ} {chi K : Coord → ℝ}
    {p : Coord} (hc : 0 < c) (hd : p 1 < b)
    (hv : 0 < ellipticWeight b c chi K p) :
    c / 2 * edgeDistance b p < K p := by
  have hdist : 0 < edgeDistance b p := sub_pos.mpr hd
  by_contra h
  have hratio : K p / edgeDistance b p ≤ c / 2 :=
    (div_le_iff₀ hdist).mpr (by linarith)
  have hz := ellipticPhi_zero hc hratio
  simp [ellipticWeight, hz] at hv

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticCutoffEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem coordLinear_norm_le (L : Coord →L[ℝ] ℝ) :
    ‖L‖ ≤ |L (Pi.single 0 1)| + |L (Pi.single 1 1)| := by
  apply L.opNorm_le_bound (add_nonneg (abs_nonneg _) (abs_nonneg _))
  intro v
  have he : v = v 0 • Pi.single 0 (1 : ℝ) + v 1 • Pi.single 1 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  have hv0 : |v 0| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0
  have hv1 : |v 1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 1
  calc
    ‖L v‖ = |v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1)| := by
      conv_lhs => rw [he]
      simp only [map_add, map_smul, smul_eq_mul, Real.norm_eq_abs]
    _ ≤ |v 0| * |L (Pi.single 0 1)| + |v 1| * |L (Pi.single 1 1)| := by
      simpa only [abs_mul] using abs_add_le
        (v 0 * L (Pi.single 0 1)) (v 1 * L (Pi.single 1 1))
    _ ≤ ‖v‖ * |L (Pi.single 0 1)| + ‖v‖ * |L (Pi.single 1 1)| :=
      add_le_add (mul_le_mul_of_nonneg_right hv0 (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hv1 (abs_nonneg _))
    _ = (|L (Pi.single 0 1)| + |L (Pi.single 1 1)|) * ‖v‖ := by ring

def ellipticEdgeRaw (c : ℝ) : Coord → ℝ :=
  ellipticWeight 0 c (fun _ => 1) (fun p => p 0)

def ellipticEdgeKernel (c : ℝ) (p : Coord) : ℝ :=
  if p 1 < 0 then ellipticEdgeRaw c p else 0

def ellipticEdgeDerivative (c : ℝ) (p : Coord) : Coord →L[ℝ] ℝ :=
  if p 1 < 0 then fderiv ℝ (ellipticEdgeRaw c) p else 0

theorem ellipticEdgeRaw_contDiffOn (c : ℝ) :
    ContDiffOn ℝ ∞ (ellipticEdgeRaw c) {p | p 1 < 0} := by
  exact ellipticWeight_contDiffOn 0 c contDiffOn_const
    (contDiffOn_apply ℝ ℝ 0 _) (fun _ h => h)

theorem ellipticEdgeHalfPlane_isOpen : IsOpen {p : Coord | p 1 < 0} :=
  isOpen_lt (continuous_apply 1) continuous_const

theorem ellipticEdgeKernel_norm_le (c : ℝ) (p : Coord) :
    ‖ellipticEdgeKernel c p‖ ≤ |p 1| ^ 6 := by
  unfold ellipticEdgeKernel
  split_ifs with hp
  · unfold ellipticEdgeRaw
    rw [Real.norm_eq_abs, abs_of_nonneg (ellipticWeight_nonneg _ _ _ _ _)]
    have h := ellipticWeight_le_distance_six 0 c (fun _ => 1) (fun p => p 0) p
      ⟨by norm_num, le_rfl⟩
    simpa only [edgeDistance, zero_sub, abs_of_neg hp] using h
  · simp

theorem ellipticEdgeKernel_hasFDerivAt_boundary (c : ℝ) {p : Coord} (hp : p 1 = 0) :
    HasFDerivAt (ellipticEdgeKernel c) (0 : Coord →L[ℝ] ℝ) p := by
  have hpzero : ellipticEdgeKernel c p = 0 := by simp [ellipticEdgeKernel, hp]
  rw [hasFDerivAt_iff_tendsto]
  simp only [hpzero, sub_zero, zero_apply]
  apply squeeze_zero (fun q => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
  · intro q
    have hcoord : |q 1| ≤ ‖q - p‖ := by
      simpa only [Pi.sub_apply, hp, sub_zero, Real.norm_eq_abs] using norm_le_pi_norm (q - p) 1
    have hb : ‖ellipticEdgeKernel c q‖ ≤ ‖q - p‖ ^ 6 :=
      (ellipticEdgeKernel_norm_le c q).trans (pow_le_pow_left₀ (abs_nonneg _) hcoord 6)
    calc
      ‖q - p‖⁻¹ * ‖ellipticEdgeKernel c q‖ ≤ ‖q - p‖⁻¹ * ‖q - p‖ ^ 6 :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg _))
      _ = ‖q - p‖ ^ 5 := by
        by_cases hz : ‖q - p‖ = 0
        · simp [hz]
        · field_simp [hz]
  · have hcont : Continuous (fun q : Coord => ‖q - p‖ ^ 5) :=
      (continuous_id.sub continuous_const).norm.pow 5
    simpa using hcont.tendsto p

theorem ellipticEdgeKernel_hasFDerivAt (c : ℝ) (p : Coord) :
    HasFDerivAt (ellipticEdgeKernel c) (ellipticEdgeDerivative c p) p := by
  rcases lt_trichotomy (p 1) 0 with hp | hp | hp
  · have hn := ellipticEdgeHalfPlane_isOpen.mem_nhds hp
    have hd := ((ellipticEdgeRaw_contDiffOn c).contDiffAt hn).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have he : ellipticEdgeKernel c =ᶠ[𝓝 p] ellipticEdgeRaw c := by
      filter_upwards [hn] with q hq
      simp [ellipticEdgeKernel, hq]
    simpa only [ellipticEdgeDerivative, hp, ite_eq_left] using hd.hasFDerivAt.congr_of_eventuallyEq he
  · simpa [ellipticEdgeDerivative, hp] using ellipticEdgeKernel_hasFDerivAt_boundary c hp
  · have hn : {q : Coord | 0 < q 1} ∈ 𝓝 p :=
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hp
    have he : ellipticEdgeKernel c =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [hn] with q hq
      simp [ellipticEdgeKernel, not_lt_of_ge hq.le]
    simpa [ellipticEdgeDerivative, not_lt_of_ge hp.le] using
      (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) p).congr_of_eventuallyEq he

def ellipticWeightC1 (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) : ℝ :=
  chi p ^ 2 * ellipticEdgeKernel c ![K p, p 1 - b]

theorem ellipticWeightC1_eq {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hp : p 1 ≤ b) : ellipticWeightC1 b c chi K p = ellipticWeight b c chi K p := by
  rcases hp.eq_or_lt with he | hl
  · simp [ellipticWeightC1, ellipticEdgeKernel, ellipticWeight, edgeDistance, he]
  · have hs : p 1 - b < 0 := sub_neg.mpr hl
    simp only [ellipticWeightC1, ellipticEdgeKernel, Matrix.cons_val_one, Matrix.cons_val_zero,
      hs, ite_eq_left, ellipticEdgeRaw, ellipticWeight, edgeDistance]
    simp only [one_pow, mul_one]
    have hd : 0 - (p 1 - b) = b - p 1 := by ring
    rw [hd]
    ring

theorem ellipticWeightC1_zero {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hp : b ≤ p 1) : ellipticWeightC1 b c chi K p = 0 := by
  simp [ellipticWeightC1, ellipticEdgeKernel, not_lt_of_ge (sub_nonneg.mpr hp)]

theorem ellipticWeightC1_nonneg (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) :
    0 ≤ ellipticWeightC1 b c chi K p := by
  by_cases hp : p 1 ≤ b
  · rw [ellipticWeightC1_eq hp]
    exact ellipticWeight_nonneg _ _ _ _ _
  · rw [ellipticWeightC1_zero (lt_of_not_ge hp).le]

theorem ellipticWeightC1_le_distance_six (b c : ℝ) (chi K : Coord → ℝ) (p : Coord)
    (hchi : 0 ≤ chi p ∧ chi p ≤ 1) :
    ellipticWeightC1 b c chi K p ≤ edgeDistance b p ^ 6 := by
  by_cases hp : p 1 ≤ b
  · rw [ellipticWeightC1_eq hp]
    exact ellipticWeight_le_distance_six _ _ _ _ _ hchi
  · rw [ellipticWeightC1_zero (lt_of_not_ge hp).le]
    positivity

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

theorem square_bound_of_abs_bound {x R : ℝ} (hx : |x| ≤ R) :
    x ^ 2 ≤ R ^ 2 := by
  calc
    x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    _ ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hx 2

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

theorem elliptic_gradient_scalar {d D a A x y : ℝ}
    (hd : 0 < d) (hdD : d ≤ D) (ha : 0 < a) (hA : a * d ≤ A) :
    d ^ 7 * (x ^ 2 + y ^ 2) ≤ (D + 1 / a) * (d ^ 6 * (x ^ 2 + A * y ^ 2)) := by
  have hD : 0 ≤ D := hd.le.trans hdD
  have hApos : 0 < A := (mul_pos ha hd).trans_le hA
  have hda : d ≤ A / a := (le_div_iff₀ ha).2 (by nlinarith)
  have hx := mul_le_mul_of_nonneg_right hdD (sq_nonneg x)
  have hy := mul_le_mul_of_nonneg_right hda (sq_nonneg y)
  have hfirst : d * (x ^ 2 + y ^ 2) ≤ D * x ^ 2 + (A / a) * y ^ 2 := by nlinarith
  have hsecond : D * x ^ 2 + (A / a) * y ^ 2 ≤
      (D + 1 / a) * (x ^ 2 + A * y ^ 2) := by
    have hgap : 0 ≤ D * A * y ^ 2 + x ^ 2 / a := by positivity
    have he : (D + 1 / a) * (x ^ 2 + A * y ^ 2) -
        (D * x ^ 2 + (A / a) * y ^ 2) = D * A * y ^ 2 + x ^ 2 / a := by ring
    linarith
  have hm := mul_le_mul_of_nonneg_left (hfirst.trans hsecond) (pow_pos hd 6).le
  nlinarith only [hm]

theorem ellipticWeight_eq_distance_six {b c c1 : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hcc : c ≤ c1) (hd : 0 < edgeDistance b p)
    (hchi : chi p = 1) (hK : c1 * edgeDistance b p ≤ K p) :
    ellipticWeight b c chi K p = edgeDistance b p ^ 6 := by
  have hratio : c ≤ K p / edgeDistance b p := by
    apply (le_div_iff₀ hd).2
    exact (mul_le_mul_of_nonneg_right hcc hd.le).trans hK
  simp [ellipticWeight, hchi, ellipticPhi_one hc hratio]

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_RegionSobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Sobolev
open SmoothLocal.Geometry SmoothLocal.Weighted

def halfOpenCoordinateRectangle (tl tr sb st : ℝ) : Set Coord :=
  {p | p 0 ∈ Ioc tl tr ∧ p 1 ∈ Ioc sb st}

def squareSobolevWeight (r : ℝ) : ℝ := 1 + 1 / (2 * r)

end SmoothLocal.Sobolev

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapGradientTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem triangular_gradient_forward_scalar {a b H x y : ℝ}
    (ha : |a| ≤ 1) (hb : 0 ≤ b) (hbH : b ≤ H) :
    (x+a*y)^2+(b*y)^2 ≤ (2+H^2)*(x^2+y^2) := by
  have hH : 0 ≤ H := hb.trans hbH
  have ha2 : a^2 ≤ 1 := (sq_le_one_iff_abs_le_one a).2 ha
  have hb2 : b^2 ≤ H^2 := (sq_le_sq₀ hb hH).2 hbH
  have hay := mul_le_mul_of_nonneg_right ha2 (sq_nonneg y)
  have hby := mul_le_mul_of_nonneg_right hb2 (sq_nonneg y)
  have hsum : (x+a*y)^2 ≤ 2*(x^2+(a*y)^2) := add_sq_le
  have hx := mul_nonneg (sq_nonneg H) (sq_nonneg x)
  nlinarith only [hay,hby,hsum,hx]

theorem triangular_gradient_inverse_scalar {a b H x y : ℝ}
    (ha : |a| ≤ 1) (hH : 0 < H) (hb : 1/H ≤ b) :
    x^2+y^2 ≤ (2+3*H^2)*((x+a*y)^2+(b*y)^2) := by
  have ha2 : a^2 ≤ 1 := (sq_le_one_iff_abs_le_one a).2 ha
  have hHb : 1 ≤ b*H := (div_le_iff₀ hH).1 hb
  have hHb2 : 1 ≤ (b*H)^2 := by
    simpa only [one_pow] using (sq_le_sq₀ (show (0:ℝ) ≤ 1 by norm_num) (by linarith : 0 ≤ b*H)).2 hHb
  have hy := mul_le_mul_of_nonneg_right hHb2 (sq_nonneg y)
  have hay := mul_le_mul_of_nonneg_right ha2 (sq_nonneg y)
  have hx : ((x+a*y)+(-a*y))^2 ≤ 2*((x+a*y)^2+(-a*y)^2) := add_sq_le
  have hgap : 0 ≤ 3*H^2*(x+a*y)^2+2*(b*y)^2 := by positivity
  nlinarith only [hy,hay,hx,hgap]

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedCutoffBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem directed_source_young_scalar {w f ut us epsilon t R c : ℝ}
    (hw : 0 ≤ w) (hc : 0 < c) (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (ht : |t| ≤ R) :
    |f * (w * (-us + epsilon * t * ut))| ≤
      c / 2 * w * (ut^2 + us^2) + ((1 + R^2) / (2 * c)) * w * f^2 := by
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have het : |epsilon * t| ≤ R := by
    rw [abs_mul, abs_of_nonneg heps]
    exact (mul_le_mul_of_nonneg_left ht heps).trans
      (by have hh := mul_le_mul_of_nonneg_right heps1 hR; simpa only [one_mul] using hh)
  have hsquare : (epsilon * t)^2 ≤ R^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (epsilon * t)) het 2
  have hyu := weighted_young c us f hc
  have hyt := weighted_young c ut (epsilon * t * f) hc
  have hraw : |f * (-us + epsilon * t * ut)| ≤
      c / 2 * (ut^2 + us^2) + (1 + R^2) / (2 * c) * f^2 := by
    have htriangle : |f * (-us + epsilon * t * ut)| ≤ |us * f| + |ut * (epsilon * t * f)| := by
      calc
        _ = |-(us * f) + ut * (epsilon * t * f)| := by congr 1; ring
        _ ≤ |us * f| + |ut * (epsilon * t * f)| := by simpa only [abs_neg] using abs_add_le (-(us * f)) (ut * (epsilon * t * f))
    have hproduct := mul_le_mul_of_nonneg_right hsquare (sq_nonneg f)
    have hdiv := div_le_div_of_nonneg_right hproduct (show 0 ≤ 2 * c by positivity)
    calc
      _ ≤ (c * us^2 + f^2 / c) / 2 + (c * ut^2 + (epsilon * t * f)^2 / c) / 2 :=
        htriangle.trans (add_le_add hyu hyt)
      _ = c / 2 * (ut^2 + us^2) + f^2 / (2 * c) + (epsilon * t)^2 * f^2 / (2 * c) := by
        field_simp [hc.ne']
        ring
      _ ≤ c / 2 * (ut^2 + us^2) + f^2 / (2 * c) + R^2 * f^2 / (2 * c) :=
        add_le_add le_rfl hdiv
      _ = _ := by ring
  have hmul := mul_le_mul_of_nonneg_left hraw hw
  calc
    _ = w * |f * (-us + epsilon * t * ut)| := by
      rw [show f * (w * (-us + epsilon * t * ut)) = w * (f * (-us + epsilon * t * ut)) by ring,
        abs_mul, abs_of_nonneg hw]
    _ ≤ w * (c / 2 * (ut^2 + us^2) + (1 + R^2) / (2 * c) * f^2) := hmul
    _ = _ := by ring

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedIntegralEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def directedForcingEnergy (chi I f : Coord → ℝ) (edge lambda : ℝ) (p : Coord) : ℝ :=
  chi p * directedWeight edge lambda I p * (f p)^2

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedFluxCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem scalarQuadratic_abs_bound {alpha beta gamma a b c x y : ℝ}
    (ha : |alpha| ≤ a) (hb : |beta| ≤ b) (hc : |gamma| ≤ c) :
    |alpha*x^2 + beta*(x*y) + gamma*y^2| ≤ (a+b+c)*(x^2+y^2) := by
  have ha0 := (abs_nonneg alpha).trans ha
  have hb0 := (abs_nonneg beta).trans hb
  have hc0 := (abs_nonneg gamma).trans hc
  have hE : 0 ≤ x^2+y^2 := add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hxy : |x*y| ≤ x^2+y^2 := by
    have hh := weighted_young 1 x y (by norm_num)
    norm_num only [one_mul, div_one] at hh
    linarith
  have hxa : |alpha| *x^2 ≤ a*(x^2+y^2) :=
    (mul_le_mul_of_nonneg_right ha (sq_nonneg x)).trans
      (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg y]) ha0)
  have hxb : |beta| *|x*y| ≤ b*(x^2+y^2) := mul_le_mul hb hxy (abs_nonneg _) hb0
  have hxc : |gamma| *y^2 ≤ c*(x^2+y^2) :=
    (mul_le_mul_of_nonneg_right hc (sq_nonneg y)).trans
      (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg x]) hc0)
  calc
    _ ≤ |alpha*x^2 + beta*(x*y)| + |gamma*y^2| := abs_add_le _ _
    _ ≤ (|alpha*x^2| + |beta*(x*y)|) + |gamma*y^2| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = |alpha| *x^2 + |beta| *|x*y| + |gamma| *y^2 := by
      rw [abs_mul alpha, abs_mul beta, abs_mul gamma, abs_of_nonneg (sq_nonneg x),
        abs_of_nonneg (sq_nonneg y)]
    _ ≤ a*(x^2+y^2)+b*(x^2+y^2)+c*(x^2+y^2) := add_le_add (add_le_add hxa hxb) hxc
    _ = _ := by ring

theorem directedFlux_scalar_bound {eta A M x y : ℝ}
    (he : |eta| ≤ 2) (hA : |A| ≤ M) :
    |-x*y + eta*x^2/2 - eta*A*y^2/2| ≤ 3*(M+1)*(x^2+y^2) ∧
    |-A*y^2/2 + eta*A*x*y + x^2/2| ≤ 3*(M+1)*(x^2+y^2) := by
  have hM : 0 ≤ M := (abs_nonneg A).trans hA
  have hetaA : |eta*A| ≤ 2*M := by
    rw [abs_mul]
    exact mul_le_mul he hA (abs_nonneg _) (by norm_num)
  have hehalf : |eta/2| ≤ (1 : ℝ) := by rw [abs_div]; norm_num; linarith
  have hAhalf : |-(A/2)| ≤ M := by rw [abs_neg, abs_div]; norm_num; linarith
  have hetaAhalf : |-(eta*A/2)| ≤ M := by
    calc
      _ = |eta*A| / 2 := by rw [abs_neg, abs_div]; norm_num
      _ ≤ M := by linarith only [hetaA]
  have hE : 0 ≤ x^2+y^2 := add_nonneg (sq_nonneg x) (sq_nonneg y)
  constructor
  · have hh := scalarQuadratic_abs_bound (x := x) (y := y) hehalf
      (show |(-1 : ℝ)| ≤ 1 by norm_num) hetaAhalf
    have heq : -x*y + eta*x^2/2 - eta*A*y^2/2 =
        (eta/2)*x^2 + (-1)*(x*y) + (-(eta*A/2))*y^2 := by ring
    rw [heq]
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) hE)
  · have hh := scalarQuadratic_abs_bound (x := x) (y := y)
      (show |(1/2 : ℝ)| ≤ 1 by norm_num) hetaA hAhalf
    have heq : -A*y^2/2 + eta*A*x*y + x^2/2 =
        (1/2)*x^2 + (eta*A)*(x*y) + (-(A/2))*y^2 := by ring
    rw [heq]
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) hE)

theorem directedWeight_le_seven {b lambda D S MI : ℝ} {I : Coord → ℝ} {p : Coord}
    (hlambda : 0 ≤ lambda) (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hI : |I p| ≤ MI) :
    directedWeight b lambda I p ≤ D * Real.exp (lambda*S+MI) * edgeDistance b p^7 := by
  have hphase : weightPhase lambda I p ≤ lambda*S+MI := by
    have hs' : -p 1 ≤ S := by linarith [(abs_le.mp hs).1]
    have hm := mul_le_mul_of_nonneg_left hs' hlambda
    unfold weightPhase
    linarith [(abs_le.mp hI).2]
  have he := Real.exp_le_exp.mpr hphase
  have hprod := mul_le_mul hdD he (Real.exp_pos _).le (hd.trans hdD)
  have hh := mul_le_mul_of_nonneg_left hprod (pow_nonneg hd 7)
  calc
    _ = edgeDistance b p^7 * (edgeDistance b p * Real.exp (weightPhase lambda I p)) := by
      unfold directedWeight
      ring
    _ ≤ edgeDistance b p^7 * (D*Real.exp (lambda*S+MI)) := hh
    _ = _ := by ring

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedDefectCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem nonnegative_cutoff_defect_bound {chi a q : ℝ}
    (hchi : 0 ≤ chi ∧ chi ≤ 1) (ha : 0 ≤ a) : chi*max 0 (a-q) ≤ a+|q| := by
  have hmax : max 0 (a-q) ≤ a+|q| := by
    apply max_le
    · exact add_nonneg ha (abs_nonneg q)
    · linarith [neg_le_abs q]
  have hh := mul_le_mul hchi.2 hmax (le_max_left (0 : ℝ) (a-q)) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using hh

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_IntegratedCapOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem directedForcingEnergy_bound
    {chi I f : Coord → ℝ} {p : Coord} {b lambda D S MI : ℝ}
    (hlambda : 0 ≤ lambda) (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hI : |I p| ≤ MI) (hchi : 0 ≤ chi p ∧ chi p ≤ 1) :
    directedForcingEnergy chi I f b lambda p ≤ D^8*Real.exp (lambda*S+MI)*(f p)^2 := by
  have hD : 0 ≤ D := hd.trans hdD
  have hW0 : 0 ≤ directedWeight b lambda I p := by unfold directedWeight; positivity
  have hW7 := directedWeight_le_seven hlambda hd hdD hs hI
  have hdpow := pow_le_pow_left₀ hd hdD 7
  have hW : directedWeight b lambda I p ≤ D^8*Real.exp (lambda*S+MI) := by
    calc
      _ ≤ D*Real.exp (lambda*S+MI)*edgeDistance b p^7 := hW7
      _ ≤ D*Real.exp (lambda*S+MI)*D^7 :=
        mul_le_mul_of_nonneg_left hdpow (by positivity)
      _ = _ := by ring
  have hchiW := mul_le_mul hchi.2 hW hW0 (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul, directedForcingEnergy] using mul_le_mul_of_nonneg_right hchiW (sq_nonneg (f p))

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_PatchFlowCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

variable {z : Coord → ℝ}
  {U : Set Coord}
variable {Y : ℝ → ℝ → ℝ} {p : Coord} {kappa : ℝ}

theorem actual_positive_curvature_strip_budget
    {G K d D c1 lambda M mu : ℝ}
    (hd : 0 < d) (hD : d ≤ D) (hc1 : 0 ≤ c1) (hlambda : 0 ≤ lambda)
    (hG : 0 ≤ G) (hGM : G ≤ M) (hK : K ≤ c1 * d)
    (hbudget : M * c1 * (lambda * D + 8) ≤ mu / 3) :
    (lambda + 8 / d) * (G * K) ≤ mu / 3 := by
  have hM : 0 ≤ M := hG.trans hGM
  have hH : 0 ≤ lambda + 8 / d := add_nonneg hlambda (div_nonneg (by norm_num) hd.le)
  have hGK : G * K ≤ M * (c1 * d) :=
    (mul_le_mul_of_nonneg_left hK hG).trans
      (mul_le_mul_of_nonneg_right hGM (mul_nonneg hc1 hd.le))
  calc
    _ ≤ (lambda + 8 / d) * (M * (c1 * d)) := mul_le_mul_of_nonneg_left hGK hH
    _ = M * c1 * (lambda * d + 8) := by field_simp [hd.ne']
    _ ≤ M * c1 * (lambda * D + 8) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hD hlambda) le_rfl) (mul_nonneg hM hc1)
    _ ≤ mu / 3 := hbudget

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowSecondVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def initialFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun s => Y s p.1) p.2

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowThirdVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def initialSecondFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun u => deriv (fun v => Y v p.1) u) p.2

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowTimeVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def timeSecondFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun u => deriv (Y p.2) u) p.1

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowLowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem abs_transport_bound {a b c M : ℝ} (hM : 0 ≤ M)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ 1) :
    |a - c * b| ≤ 2 * M := by
  calc
    _ ≤ |a| + |c| * |b| := by simpa only [abs_mul] using abs_sub a (c * b)
    _ ≤ M + 1 * M := add_le_add ha (by
      simpa only [mul_comm] using mul_le_mul hb hc (abs_nonneg _) hM)
    _ = 2 * M := by ring

theorem abs_second_initial_coefficient_bound {a b c d M : ℝ} (hM : 0 ≤ M)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ 1) (hd : |d| ≤ M) :
    |-a + b * c + d^2| ≤ 2 * M + M^2 := by
  have hbase : |-a + b * c| ≤ 2 * M := by
    calc
      _ = |-(a - c * b)| := by congr 1; ring
      _ = |a - c * b| := abs_neg _
      _ ≤ 2 * M := abs_transport_bound hM ha hb hc
  have hsq : |d^2| ≤ M^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  exact (abs_add_le _ _).trans (add_le_add hbase hsq)

theorem abs_third_time_coefficient_bound {a00 a10 a01 a11 a0 a1 c M : ℝ}
    (hM : 0 ≤ M) (hc : |c| ≤ 1)
    (h00 : |a00| ≤ M) (h10 : |a10| ≤ M) (h01 : |a01| ≤ M)
    (h11 : |a11| ≤ M) (h0 : |a0| ≤ M) (h1 : |a1| ≤ M) :
    |-a00 + c * a10 + (a01 - c * a11) * c + a1 * (a0 - c * a1)| ≤
      4 * M + 2 * M^2 := by
  have ha : |-a00 + c * a10| ≤ 2 * M := by
    calc
      _ = |-(a00 - c * a10)| := by congr 1; ring
      _ = |a00 - c * a10| := abs_neg _
      _ ≤ 2 * M := abs_transport_bound hM h00 h10 hc
  have hb := abs_transport_bound hM h01 h11 hc
  have hd := abs_transport_bound hM h0 h1 hc
  calc
    _ ≤ |-a00 + c * a10| + |a01 - c * a11| * |c| + |a1| * |a0 - c * a1| := by
      simpa only [abs_mul] using (abs_add_le (-a00 + c * a10 + (a01 - c * a11) * c)
        (a1 * (a0 - c * a1))).trans
          (add_le_add (abs_add_le (-a00 + c * a10) ((a01 - c * a11) * c)) le_rfl)
    _ ≤ 2 * M + (2 * M) * 1 + M * (2 * M) :=
      add_le_add (add_le_add ha (mul_le_mul hb hc (abs_nonneg _) (by positivity)))
        (mul_le_mul h1 hd (abs_nonneg _) hM)
    _ = 4 * M + 2 * M^2 := by ring

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_PhysicalCapTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem scalar_two_integral_transport
    {a b H J F U Fp Up P Q : ℝ} (hH : 0 ≤ H) (hJ : 0 ≤ J)
    (hF : 0 ≤ F) (hU : 0 ≤ U) (hFp : 0 ≤ Fp) (hUp : 0 ≤ Up)
    (hFle : F ≤ H*Fp) (hUle : U ≤ H*Up)
    (hP : P ≤ a*F+b*U) (hQ : Q ≤ J*P) :
    Q ≤ J*H*(|a|+|b|+1)*(Fp+Up) := by
  have habs : a*F+b*U ≤ |a| *F+|b| *U :=
    add_le_add (mul_le_mul_of_nonneg_right (le_abs_self a) hF)
      (mul_le_mul_of_nonneg_right (le_abs_self b) hU)
  have harea : |a| *F+|b| *U ≤ H*(|a| *Fp+|b| *Up) := by
    calc
      _ ≤ |a| *(H*Fp)+|b| *(H*Up) :=
        add_le_add (mul_le_mul_of_nonneg_left hFle (abs_nonneg a))
          (mul_le_mul_of_nonneg_left hUle (abs_nonneg b))
      _ = _ := by ring
  have hsum : |a| *Fp+|b| *Up ≤ (|a|+|b|+1)*(Fp+Up) := by
    have h1 := mul_nonneg (abs_nonneg a) hUp
    have h2 := mul_nonneg (abs_nonneg b) hFp
    nlinarith only [h1,h2,hFp,hUp]
  calc
    Q ≤ J*P := hQ
    _ ≤ J*(a*F+b*U) := mul_le_mul_of_nonneg_left hP hJ
    _ ≤ J*(|a| *F+|b| *U) := mul_le_mul_of_nonneg_left habs hJ
    _ ≤ J*(H*(|a| *Fp+|b| *Up)) := mul_le_mul_of_nonneg_left harea hJ
    _ ≤ J*(H*((|a|+|b|+1)*(Fp+Up))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hH) hJ
    _ = _ := by ring

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualRemainderFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def heightStateBaseOrder : Fin 4 → ℕ := ![1, 1, 2, 2]
def heightComponentIndex : Fin 4 → Fin 6 := ![2, 3, 4, 5]

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_MixedDarbouxElimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def mixedBlockWord (ds : List (Fin 2)) (c : OrderedFinpartition ds.length)
    (j : Fin c.length) : List (Fin 2) := List.ofFn (fun i => ds.get (c.emb j i))

def heightStateSuffix : Fin 4 → List (Fin 2) := ![[0], [1], [0, 1], [1, 1]]

theorem heightStateSuffix_length (i : Fin 4) :
    (heightStateSuffix i).length = heightStateBaseOrder i := by
  fin_cases i <;> rfl

theorem mixed_nonfull_height_word_length (ds : List (Fin 2)) (hds : 0 < ds.length)
    (c : OrderedFinpartition ds.length) (hc : c ≠ fullBlockPartition ds.length hds)
    (j : Fin c.length) (i : Fin 4) :
    (mixedBlockWord ds c j ++ heightStateSuffix i).length ≤ ds.length + 1 := by
  have hsize := ordered_nonfull_partSize_le hds c hc j
  have hbase : heightStateBaseOrder i ≤ 2 := by fin_cases i <;> (first | (simp [heightStateBaseOrder]; all_goals first | (norm_num [heightStateBaseOrder]; done) | rfl | decide) | (norm_num [heightStateBaseOrder]; done) | norm_num [heightStateBaseOrder])
  simp only [List.length_append, mixedBlockWord, List.length_ofFn, heightStateSuffix_length]
  omega

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_ActualRemainderL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def chainProductL2Budget (B : ℝ) (H : ℝ≥0) (V : Set Coord) (ell : ℕ) : ℝ≥0∞ :=
  ‖B ^ ell‖ₑ * ((H : ℝ≥0∞) + (volume V) ^ (1 / (2 : ℝ)))

def firstJetPairL2Budget (C : ℝ) (H : ℝ≥0) : ℝ≥0∞ :=
  ‖C‖ₑ * (H : ℝ≥0∞) + ‖C‖ₑ * (H : ℝ≥0∞)

theorem enorm_pow_mono_of_one_le {B : ℝ} (hB : 1 ≤ B) {a b : ℕ} (hab : a ≤ b) :
    ‖B ^ a‖ₑ ≤ ‖B ^ b‖ₑ := by
  rw [enorm_le_iff_norm_le, Real.norm_of_nonneg (pow_nonneg (by linarith) _),
    Real.norm_of_nonneg (pow_nonneg (by linarith) _)]
  exact pow_le_pow_right₀ hB hab

theorem chainProductL2Budget_lt_top (B : ℝ) (H : ℝ≥0) {V : Set Coord}
    (hVfinite : volume V < (⊤ : ℝ≥0∞)) (ell : ℕ) : chainProductL2Budget B H V ell < (⊤ : ℝ≥0∞) := by
  unfold chainProductL2Budget
  exact ENNReal.mul_lt_top (by finiteness)
    (ENNReal.add_lt_top.mpr ⟨by finiteness,
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hVfinite.ne⟩)

theorem scalar_coefficient_eLpNorm_two {V : Set Coord} (hV : MeasurableSet V)
    {a f : Coord → ℝ} {C : ℝ} (hC : 0 ≤ C) (ha : ∀ p ∈ V, |a p| ≤ C) :
    eLpNorm' (fun p => a p * f p) (2 : ℝ) (volume.restrict V) ≤
      ‖C‖ₑ * eLpNorm' f (2 : ℝ) (volume.restrict V) := by
  have hdom : ∀ᵐ p ∂(volume.restrict V), ‖a p * f p‖ ≤ ‖C * f p‖ := by
    filter_upwards [ae_restrict_mem hV] with p hp
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (ha p hp) (abs_nonneg _)
  calc
    _ ≤ eLpNorm' (fun p => C * f p) (2 : ℝ) (volume.restrict V) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := eLpNorm'_const_smul (𝕜 := ℝ) (F := ℝ) (f := f) C (by norm_num)

theorem scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
    {V : Set Coord} (hV : MeasurableSet V)
    {a f : Coord → ℝ} {C : ℝ} (hC : 0 ≤ C) (ha : ∀ p ∈ V, |a p| ≤ C)
    (hmeas : AEStronglyMeasurable (fun p => a p * f p) (volume.restrict V)) :
    eLpNorm (fun p => a p * f p) 2 (volume.restrict V) ≤
      ‖C‖ₑ * eLpNorm f 2 (volume.restrict V) := by
  have hraw : eLpNorm' f (2 : ℝ) (volume.restrict V) ≤
      eLpNorm f 2 (volume.restrict V) := by
    by_cases hf : AEStronglyMeasurable f (volume.restrict V)
    · rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
    · rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  calc
    _ = eLpNorm' (fun p => a p * f p) (2 : ℝ) (volume.restrict V) := by
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
    _ ≤ ‖C‖ₑ * eLpNorm' f (2 : ℝ) (volume.restrict V) :=
      scalar_coefficient_eLpNorm_two hV hC ha
    _ ≤ _ := mul_le_mul' le_rfl hraw

theorem bounded_real_eLpNorm_two {V : Set Coord} (hV : MeasurableSet V)
    {f : Coord → ℝ} {B : ℝ} (hB : 0 ≤ B) (hf : ∀ p ∈ V, ‖f p‖ ≤ B) :
    eLpNorm' f (2 : ℝ) (volume.restrict V) ≤ ‖B‖ₑ * (volume V) ^ (1 / (2 : ℝ)) := by
  have hdom : ∀ᵐ p ∂(volume.restrict V), ‖f p‖ ≤ ‖B‖ := by
    filter_upwards [ae_restrict_mem hV] with p hp
    simpa only [Real.norm_of_nonneg hB] using hf p hp
  calc
    _ ≤ eLpNorm' (fun _ : Coord => B) (2 : ℝ) (volume.restrict V) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := by
      rw [eLpNorm'_const B (by norm_num), Measure.restrict_apply_univ]

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_MixedRemainderFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem fullJet_fixed_input_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord → E} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (n : ℕ) (v : Fin n → Coord) :
    ContinuousOn (fun p => iteratedFDeriv ℝ n f p v) U := by
  intro p hp
  have hD := ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)).continuousAt
  have hev := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Coord) E v).continuous.continuousAt
    (x := iteratedFDeriv ℝ n f p)
  exact (hev.comp hD).continuousWithinAt

theorem fullJet_coordinate_projection_abs_le_one {n : ℕ} (hn : 0 < n)
    (d : Fin n → Fin 2) (i : Fin 2) (p : Coord) :
    |iteratedFDeriv ℝ n (fun q : Coord => q i) p (fun j => Pi.single (d j) (1 : ℝ))| ≤ 1 := by
  by_cases hn1 : n = 1
  · subst n
    change |iteratedFDeriv ℝ 1 (ContinuousLinearMap.proj i : Coord →L[ℝ] ℝ) p _| ≤ 1
    rw [iteratedFDeriv_one_apply, ContinuousLinearMap.fderiv]
    simp only [ContinuousLinearMap.proj_apply, Pi.single_apply]
    split_ifs <;> norm_num
  · change |iteratedFDeriv ℝ n (ContinuousLinearMap.proj i : Coord →L[ℝ] ℝ) p _| ≤ 1
    rw [fullJet_linear_zero _ (by omega)]
    norm_num

theorem mixed_high_factor_unique {k : ℕ} (hk : 5 ≤ k)
    (c : OrderedFinpartition k) (r : Fin c.length → Fin 6) {i j : Fin c.length}
    (hi : k ≤ c.partSize i + stateBaseOrder (r i))
    (hj : k ≤ c.partSize j + stateBaseOrder (r j)) : i = j := by
  by_contra hij
  have hb := ordered_two_partSizes_le c hij
  have hbi := stateBaseOrder_le_two (r i)
  have hbj := stateBaseOrder_le_two (r j)
  omega

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MixedDerivativeL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem word_no_x_eq_replicate (ds : List (Fin 2)) (hx : ds.count 0 = 0) :
    ds = List.replicate ds.length 1 := by
  apply List.eq_replicate_iff.mpr
  refine ⟨rfl, ?_⟩
  intro i hi
  fin_cases i
  · have hpos : 0 < ds.count 0 := List.count_pos_iff.mpr hi
    omega
  · rfl

def mixedXBudget (C : ℝ) (R : ℝ≥0∞) (Htop : ℝ≥0) : ℕ → ℝ≥0∞
  | 0 => (Htop : ℝ≥0∞) + R
  | n + 1 => (1 + ‖C‖ₑ + ‖C‖ₑ) * mixedXBudget C R Htop n

theorem mixedXBudget_monotone (C : ℝ) (R : ℝ≥0∞) (Htop : ℝ≥0) :
    Monotone (mixedXBudget C R Htop) := by
  apply monotone_nat_of_le_succ
  intro n
  have h : (1 : ℝ≥0∞) ≤ 1 + ‖C‖ₑ + ‖C‖ₑ :=
    (le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_right (by positivity))
  calc
    mixedXBudget C R Htop n = 1 * mixedXBudget C R Htop n := (one_mul _).symm
    _ ≤ (1 + ‖C‖ₑ + ‖C‖ₑ) * mixedXBudget C R Htop n := mul_le_mul' h le_rfl
    _ = mixedXBudget C R Htop (n + 1) := rfl

theorem mixedXBudget_base_le (C : ℝ) (R : ℝ≥0∞) (Htop : ℝ≥0) (n : ℕ) :
    (Htop : ℝ≥0∞) + R ≤ mixedXBudget C R Htop n :=
  mixedXBudget_monotone C R Htop (Nat.zero_le n)

theorem mixedXBudget_step (C : ℝ) (R : ℝ≥0∞) (Htop : ℝ≥0) (n : ℕ)
    {a b : ℝ≥0∞} (ha : a ≤ mixedXBudget C R Htop n)
    (hb : b ≤ mixedXBudget C R Htop n) :
    ‖C‖ₑ * a + ‖C‖ₑ * b + R ≤ mixedXBudget C R Htop (n + 1) := by
  have hR : R ≤ mixedXBudget C R Htop n :=
    (le_add_of_nonneg_left (by positivity)).trans (mixedXBudget_base_le C R Htop n)
  calc
    _ ≤ ‖C‖ₑ * mixedXBudget C R Htop n +
        ‖C‖ₑ * mixedXBudget C R Htop n + mixedXBudget C R Htop n :=
      add_le_add (add_le_add (mul_le_mul' le_rfl ha) (mul_le_mul' le_rfl hb)) hR
    _ = mixedXBudget C R Htop (n + 1) := by rw [mixedXBudget]; ring

theorem mixedXBudget_lt_top (C : ℝ) {R : ℝ≥0∞} (hR : R < (⊤ : ℝ≥0∞))
    (Htop : ℝ≥0) (n : ℕ) : mixedXBudget C R Htop n < (⊤ : ℝ≥0∞) := by
  induction n with
  | zero => simpa only [mixedXBudget] using ENNReal.add_lt_top.mpr ⟨by finiteness, hR⟩
  | succ n ih =>
      change (1 + ‖C‖ₑ + ‖C‖ₑ) * mixedXBudget C R Htop n < (⊤ : ℝ≥0∞)
      exact ENNReal.mul_lt_top (by finiteness) ih

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_FixedMetricRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

theorem compact_finite_fullJet_bound
    {f : Coord → ℝ} {U S : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (ell : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ ell, ∀ p ∈ S, ‖iteratedFDeriv ℝ k f p‖ ≤ M := by
  classical
  have hk : ∀ k : Fin (ell + 1), ∃ A : ℝ, ∀ p ∈ S, ‖iteratedFDeriv ℝ k.val f p‖ ≤ A := by
    intro k
    have hcont : ContinuousOn (iteratedFDeriv ℝ k.val f) S := by
      intro p hp
      exact (((hf.contDiffAt (hU.mem_nhds (hSU hp))).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k.val)).continuousAt).continuousWithinAt
    exact hS.exists_bound_of_continuousOn hcont
  choose A hA using hk
  refine ⟨∑ k : Fin (ell + 1), |A k|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro k hk p hp
  let j : Fin (ell + 1) := ⟨k, by omega⟩
  exact (hA j p hp).trans ((le_abs_self (A j)).trans
    (Finset.single_le_sum (fun index _ => abs_nonneg (A index)) (Finset.mem_univ j)))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_RemainderAreaBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow

theorem chainProductL2Budget_mono_area (B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (ell : ℕ) :
    chainProductL2Budget B H V ell ≤ chainProductL2Budget B H W ell :=
  mul_le_mul' le_rfl (add_le_add le_rfl
    (ENNReal.rpow_le_rpow hVW (by norm_num : 0 ≤ (1 / (2 : ℝ)))))

theorem mixedXBudget_mono_remainder (C : ℝ) {R S : ℝ≥0∞} (hRS : R ≤ S)
    (Htop : ℝ≥0) (n : ℕ) : mixedXBudget C R Htop n ≤ mixedXBudget C S Htop n := by
  induction n with
  | zero => exact add_le_add le_rfl hRS
  | succ _ ih => exact mul_le_mul' le_rfl ih

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapInductionData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Sobolev

variable {bStar : ℝ}

theorem compact_continuous_memLp_two {f : Coord → ℝ} {V : Set Coord}
    (hV : IsCompact V) (hf : ContinuousOn f V) : MemLp f 2 (volume.restrict V) :=
  (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable hV.isClosed.measurableSet)).mpr
    ((hf.pow 2).integrableOn_compact hV)

theorem integral_each_sq_le_sum {f h : Coord → ℝ} {V : Set Coord}
    (hV : IsCompact V) (hf : ContinuousOn f V) (hh : ContinuousOn h V) :
    (∫ p in V, (f p)^2) ≤ ∫ p in V, (f p)^2+(h p)^2 ∧
      (∫ p in V, (h p)^2) ≤ ∫ p in V, (f p)^2+(h p)^2 := by
  have hfI : IntegrableOn (fun p => (f p)^2) V volume := (hf.pow 2).integrableOn_compact hV
  have hhI : IntegrableOn (fun p => (h p)^2) V volume := (hh.pow 2).integrableOn_compact hV
  exact ⟨setIntegral_mono_on hfI (hfI.add hhI) hV.isClosed.measurableSet
      (fun p hp => le_add_of_nonneg_right (sq_nonneg _)),
    setIntegral_mono_on hhI (hfI.add hhI) hV.isClosed.measurableSet
      (fun p hp => le_add_of_nonneg_left (sq_nonneg _))⟩

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapReflectionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Model

def reflectionMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,-1]

theorem reflectionMatrix_square : reflectionMatrix * reflectionMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [reflectionMatrix,Matrix.mul_apply,Fin.sum_univ_two]; all_goals first | (norm_num [reflectionMatrix,Matrix.mul_apply,Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [reflectionMatrix,Matrix.mul_apply,Fin.sum_univ_two]; done) | norm_num [reflectionMatrix,Matrix.mul_apply,Fin.sum_univ_two])

@[simp] theorem reflectionMatrix_det : reflectionMatrix.det = -1 := by
  norm_num [reflectionMatrix,Matrix.det_fin_two]

theorem reflectionMatrix_isUnit : IsUnit reflectionMatrix := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  apply isUnit_iff_ne_zero.mpr
  rw [reflectionMatrix_det]
  norm_num

@[simp] theorem reflectionMatrix_inv : reflectionMatrix⁻¹ = reflectionMatrix :=
  Matrix.inv_eq_left_inv reflectionMatrix_square

end SmoothLocal.Flow.Reflection

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EnergyCauchySchwarz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace SmoothLocal.Hyperbolic

theorem integral_square_eq_L2_norm_square
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : (∫ x, f x ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  calc
    (∫ x, f x ^ 2 ∂μ) = ∫ x, inner ℝ (hf.toLp f x) (hf.toLp f x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := rfl
    _ = ‖hf.toLp f‖ ^ 2 := real_inner_self_eq_norm_sq _

theorem sqrt_integral_square_eq_L2_norm
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : Real.sqrt (∫ x, f x ^ 2 ∂μ) = ‖hf.toLp f‖ := by
  rw [integral_square_eq_L2_norm_square hf, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem integral_product_abs_le_sqrt_squares
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have he : (∫ x, f x * g x ∂μ) = inner ℝ (hf.toLp f) (hg.toLp g) := by
    change (∫ x, f x * g x ∂μ) = ∫ x, inner ℝ (hf.toLp f x) (hg.toLp g x) ∂μ
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    simp only [hfx, hgx, Real.inner_apply]
  rw [he, sqrt_integral_square_eq_L2_norm hf, sqrt_integral_square_eq_L2_norm hg]
  exact abs_real_inner_le_norm _ _

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_UpperCapWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

structure UpperCapRectangle (floor : ℝ) where
  left : ℝ
  right : ℝ
  bottom : ℝ
  top : ℝ
  left_gt : -2 < left
  right_lt : right < 2
  top_lt : top < 2
  horizontal : left ≤ right
  vertical : bottom ≤ top
  bottom_gt : floor < bottom
  floor_nonneg : 0 ≤ floor

end SmoothLocal.Flow.Reflection

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricPBundleBounds
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

section FiniteProducts
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_pi_le {ι : Type*} [Fintype ι]
    {f : E → ι → F} {p : E} (hf : ContDiffAt ℝ ∞ f p)
    (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ i, ‖iteratedFDeriv ℝ n (fun x => f x i) p‖ ≤ M) :
    ‖iteratedFDeriv ℝ n f p‖ ≤ M := by
  have heq : iteratedFDeriv ℝ n f p =
      ContinuousMultilinearMap.pi (fun i => iteratedFDeriv ℝ n (fun x => f x i) p) := by
    ext v i
    have hh := congrArg (fun L => L v)
      ((ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F).iteratedFDeriv_comp_left
        hf (WithTop.coe_le_coe.mpr le_top) (i := n))
    exact hh.symm
  rw [heq, ContinuousMultilinearMap.opNorm_pi]
  exact (pi_norm_le_iff_of_nonneg hM).mpr hb

theorem norm_iteratedFDeriv_prod_le {f : E → F} {g : E → G} {p : E}
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (n : ℕ) {M : ℝ}
    (hfB : ‖iteratedFDeriv ℝ n f p‖ ≤ M)
    (hgB : ‖iteratedFDeriv ℝ n g p‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun x => (f x, g x)) p‖ ≤ M := by
  rw [iteratedFDeriv_prodMk hf hg (WithTop.coe_le_coe.mpr le_top),
    ContinuousMultilinearMap.opNorm_prod]
  exact max_le hfB hgB

theorem norm_iteratedFDeriv_comp_contraction
    (L : E →L[ℝ] F) {f : F → G} {U : Set F}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hL : ‖L‖ ≤ 1)
    {p : E} (hp : L p ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ L) p‖ ≤ ‖iteratedFDeriv ℝ n f (L p)‖ := by
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  rw [← iteratedFDerivWithin_of_isOpen n hpre hp,
    L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hp
      (WithTop.coe_le_coe.mpr le_top),
    iteratedFDerivWithin_of_isOpen n hU hp]
  exact ((iteratedFDeriv ℝ n f (L p)).norm_compContinuousLinearMap_le
    (fun _ => L)).trans (by
      calc
        _ ≤ ‖iteratedFDeriv ℝ n f (L p)‖ * ∏ _ : Fin n, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => norm_nonneg L)
            (fun _ _ => hL)) (norm_nonneg _)
        _ = _ := by simp)

theorem norm_iteratedFDeriv_id_pos (p : E) {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun x : E => x) p‖ ≤ 1 := by
  cases n with
  | zero => omega
  | succ n =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (fun x : E => x) = (fun _ : E => ContinuousLinearMap.id ℝ E) := by
      funext x
      exact fderiv_fun_id
    rw [he]
    cases n with
    | zero => simpa using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
    | succ n => simp only [iteratedFDeriv_succ_const] <;> norm_num
end FiniteProducts

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_UpperCapMetricJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

abbrev UpperCapMetricJetBudget (floor : ℝ) := ℕ → UpperCapRectangle floor → ℝ

end SmoothLocal.Flow.Reflection

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseDerivativeBounds
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

theorem axisBump_derivative_bound_exists {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∃ C : ℝ, ∀ t, ‖iteratedFDeriv ℝ k (axisBump a) t‖ ≤ C :=
  ((axisBump_contDiff a).continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).bounded_above_of_compact_support
    ((axisBump_hasCompactSupport ha).iteratedFDeriv k)

def axisBumpDerivativeBound (a : ℝ) (ha : 0 < a) (k : ℕ) : ℝ :=
  1 + |Classical.choose (axisBump_derivative_bound_exists ha k)|

theorem axisBumpDerivativeBound_pos {a : ℝ} (ha : 0 < a) (k : ℕ) :
    0 < axisBumpDerivativeBound a ha k := by
  unfold axisBumpDerivativeBound
  positivity

theorem axisBump_derivative_le {a : ℝ} (ha : 0 < a) (k : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (axisBump a) t‖ ≤ axisBumpDerivativeBound a ha k := by
  have hc := Classical.choose_spec (axisBump_derivative_bound_exists ha k) t
  have habs := le_abs_self (Classical.choose (axisBump_derivative_bound_exists ha k))
  unfold axisBumpDerivativeBound
  linarith

def derivativeConvolution (A B : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A i * B (k - i)

theorem derivativeConvolution_nonneg {A B : ℕ → ℝ}
    (hA : ∀ k, 0 ≤ A k) (hB : ∀ k, 0 ≤ B k) (k : ℕ) :
    0 ≤ derivativeConvolution A B k :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _))

def pulseCoreDerivativeBound (a : ℝ) (ha : 0 < a) : ℕ → ℝ :=
  derivativeConvolution
    (derivativeConvolution (axisBumpDerivativeBound a ha)
      (axisBumpDerivativeBound (1 / 2) (by norm_num))) (fun _ => 1)

theorem pulseCoreDerivativeBound_nonneg {a : ℝ} (ha : 0 < a) (k : ℕ) :
    0 ≤ pulseCoreDerivativeBound a ha k :=
  derivativeConvolution_nonneg
    (derivativeConvolution_nonneg (fun _ => (axisBumpDerivativeBound_pos ha _).le)
      (fun _ => (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ) < 1 / 2) _).le))
    (fun _ => zero_le_one) k

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

theorem pulse_support_eventually (q0 a delta : ℝ) (hq : |q0| * a < 1 / 10) :
    ∀ᶠ tau : ℝ in atTop, delta / (2 * tau) + |q0| * a < 1 / 10 := by
  have h : Tendsto (fun tau : ℝ => delta / (2 * tau) + |q0| * a)
      atTop (𝓝 (|q0| * a)) := by
    have hi := (tendsto_inv_atTop_zero : Tendsto (fun tau : ℝ => tau⁻¹) atTop (𝓝 0))
    simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using
      (hi.const_mul (delta / 2)).add_const (|q0| * a)
  exact h.eventually_lt tendsto_const_nhds hq

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_PulseClosureApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise Distributions

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

def metricApproximationAccuracy (tau : ℕ) : ℝ := 1 / ((tau : ℝ)^tau)

theorem metricApproximationAccuracy_pos {tau : ℕ} (htau : 0 < tau) :
    0 < metricApproximationAccuracy tau :=
  one_div_pos.mpr (pow_pos (Nat.cast_pos.mpr htau) tau)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_ExteriorAnnuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

def roundDistance (c p : Coord) : ℝ :=
  dist (euclideanPlaneCoordinates p) (euclideanPlaneCoordinates c)

theorem roundDistance_sq (c p : Coord) : roundDistance c p ^ 2 = roundRadiusSq c p :=
  euclideanPlaneCoordinates_dist_sq p c

theorem roundDistance_nonneg (c p : Coord) : 0 ≤ roundDistance c p := dist_nonneg

theorem roundDistance_continuous (c : Coord) : Continuous (roundDistance c) :=
  euclideanPlaneCoordinates.continuous.dist continuous_const

theorem mem_roundClosedDisk_iff_roundDistance (c p : Coord) {r : ℝ} (hr : 0 ≤ r) :
    p ∈ roundClosedDisk c r ↔ roundDistance c p ≤ r := by
  rw [roundClosedDisk_eq_preimage_closedBall c hr]
  rfl

theorem frontier_roundDistance_eq (c p : Coord) {r : ℝ} (hr : 0 < r)
    (hp : p ∈ frontier (roundClosedDisk c r)) : roundDistance c p = r := by
  apply (sq_eq_sq₀ (roundDistance_nonneg c p) hr.le).mp
  rw [roundDistance_sq]
  exact (mem_frontier_roundClosedDisk_iff c p hr).mp hp

def exteriorLayerInner (n k : ℕ) : ℝ :=
  accumulatingRadius n * (1 + (3 / 4 : ℝ) * accumulatingScale k)

def exteriorLayerOuter (n k : ℕ) : ℝ :=
  accumulatingRadius n * (1 + accumulatingScale k)

def exteriorLayerMiddle (n k : ℕ) : ℝ :=
  accumulatingRadius n * (1 + (7 / 8 : ℝ) * accumulatingScale k)

def exteriorClosedLayer (n k : ℕ) : Set Coord := {p |
  exteriorLayerInner n k ≤ roundDistance (accumulatingCenter n) p ∧
    roundDistance (accumulatingCenter n) p ≤ exteriorLayerOuter n k}

def exteriorOpenLayer (n k : ℕ) : Set Coord := {p |
  exteriorLayerInner n k < roundDistance (accumulatingCenter n) p ∧
    roundDistance (accumulatingCenter n) p < exteriorLayerOuter n k}

theorem exteriorLayer_radii (n k : ℕ) :
    accumulatingRadius n < exteriorLayerInner n k ∧
      exteriorLayerInner n k < exteriorLayerMiddle n k ∧
      exteriorLayerMiddle n k < exteriorLayerOuter n k ∧
      exteriorLayerOuter n k < 2 * accumulatingRadius n := by
  have hr := accumulatingRadius_pos n
  have ha := accumulatingScale_pos k
  have hab := accumulatingScale_le_half k
  have hra := mul_pos hr ha
  unfold exteriorLayerInner exteriorLayerMiddle exteriorLayerOuter
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem exteriorOpenLayer_isOpen (n k : ℕ) : IsOpen (exteriorOpenLayer n k) :=
  (isOpen_lt continuous_const (roundDistance_continuous _)).inter
    (isOpen_lt (roundDistance_continuous _) continuous_const)

theorem exteriorOpenLayer_subset_closed (n k : ℕ) :
    exteriorOpenLayer n k ⊆ exteriorClosedLayer n k := fun _ hp => ⟨hp.1.le, hp.2.le⟩

theorem exteriorClosedLayer_outside_disk (n k : ℕ) :
    Disjoint (exteriorClosedLayer n k) (accumulatingDisk n) := by
  apply Set.disjoint_left.mpr
  intro p hp hd
  have hrad := (mem_roundClosedDisk_iff_roundDistance _ _ (accumulatingRadius_pos n).le).mp hd
  have hlo := (exteriorLayer_radii n k).1
  exact (not_le_of_gt hlo) (hp.1.trans hrad)

theorem exteriorClosedLayer_subset_enlarged (n k : ℕ) :
    exteriorClosedLayer n k ⊆ enlargedAccumulatingDisk n := by
  intro p hp
  apply (mem_roundClosedDisk_iff_roundDistance _ _
    (mul_pos (by norm_num) (accumulatingRadius_pos n)).le).mpr
  exact (hp.2.trans_lt (exteriorLayer_radii n k).2.2.2).le

theorem exteriorLayer_separated {k l : ℕ} (n : ℕ) (hkl : k < l) :
    exteriorLayerOuter n l < exteriorLayerInner n k := by
  have ha := accumulatingScale_le_half_of_lt hkl
  have hpos := mul_pos (accumulatingRadius_pos n) (accumulatingScale_pos k)
  have hmul := mul_le_mul_of_nonneg_left ha (accumulatingRadius_pos n).le
  unfold exteriorLayerOuter exteriorLayerInner
  nlinarith

theorem exteriorClosedLayers_pairwise_disjoint (n : ℕ) :
    Pairwise (fun k l => Disjoint (exteriorClosedLayer n k) (exteriorClosedLayer n l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro p hp hk
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · exact (not_le_of_gt (exteriorLayer_separated n hlt)) (hp.1.trans hk.2)
  · exact (not_le_of_gt (exteriorLayer_separated n hgt)) (hk.1.trans hp.2)

theorem exteriorClosedLayers_disjoint_different_disks {n m : ℕ}
    (hnm : n ≠ m) (k l : ℕ) : Disjoint (exteriorClosedLayer n k) (exteriorClosedLayer m l) :=
  (enlargedAccumulatingDisks_pairwise_disjoint hnm).mono
    (exteriorClosedLayer_subset_enlarged n k) (exteriorClosedLayer_subset_enlarged m l)

def radialLift (c : Coord) (s : ℝ) (p : Coord) : Coord := c + s • (p - c)

theorem roundDistance_radialLift (c p : Coord) (s : ℝ) :
    roundDistance c (radialLift c s p) = |s| * roundDistance c p := by
  simp only [roundDistance, radialLift, dist_eq_norm, map_add, map_smul, map_sub,
    add_sub_cancel_left, norm_smul, Real.norm_eq_abs]

def exteriorMiddleLift (n k : ℕ) (p : Coord) : Coord :=
  radialLift (accumulatingCenter n) (1 + (7 / 8 : ℝ) * accumulatingScale k) p

theorem exteriorMiddleLift_mem_layer (n k : ℕ) {p : Coord}
    (hp : p ∈ frontier (accumulatingDisk n)) :
    exteriorMiddleLift n k p ∈ exteriorOpenLayer n k := by
  have hr := frontier_roundDistance_eq (accumulatingCenter n) p (accumulatingRadius_pos n) hp
  have hs : 0 ≤ 1 + (7 / 8 : ℝ) * accumulatingScale k := by
    have := accumulatingScale_pos k
    positivity
  have hrad : roundDistance (accumulatingCenter n) (exteriorMiddleLift n k p) =
      exteriorLayerMiddle n k := by
    rw [exteriorMiddleLift, roundDistance_radialLift, abs_of_nonneg hs, hr]
    unfold exteriorLayerMiddle
    ring
  change exteriorLayerInner n k < _ ∧ _ < exteriorLayerOuter n k
  rw [hrad]
  exact ⟨(exteriorLayer_radii n k).2.1, (exteriorLayer_radii n k).2.2.1⟩

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_ExteriorCenterNets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

theorem accumulatingDisk_frontier_isCompact (n : ℕ) :
    IsCompact (frontier (accumulatingDisk n)) := by
  apply (accumulatingDisk_isCompact n).of_isClosed_subset isClosed_frontier
  simpa only [(accumulatingDisk_isCompact n).isClosed.closure_eq] using
    (frontier_subset_closure : frontier (accumulatingDisk n) ⊆ closure (accumulatingDisk n))

theorem exists_finite_disk_boundary_net (n k : ℕ) :
    ∃ s : Finset Coord, (∀ p ∈ s, p ∈ frontier (accumulatingDisk n)) ∧
      ∀ p ∈ frontier (accumulatingDisk n), ∃ q ∈ s, dist p q < accumulatingScale k := by
  classical
  obtain ⟨s, hsfront, hsfin, hcover⟩ :=
    (accumulatingDisk_frontier_isCompact n).finite_cover_balls (accumulatingScale_pos k)
  refine ⟨hsfin.toFinset, ?_, ?_⟩
  · intro p hp
    exact hsfront (hsfin.mem_toFinset.mp hp)
  · intro p hp
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (hcover hp)
    obtain ⟨hqs, hpq⟩ := Set.mem_iUnion.mp hq
    exact ⟨q, hsfin.mem_toFinset.mpr hqs, hpq⟩

def diskBoundaryNet (n k : ℕ) : Finset Coord :=
  Classical.choose (exists_finite_disk_boundary_net n k)

theorem diskBoundaryNet_mem_frontier (n k : ℕ) {p : Coord} (hp : p ∈ diskBoundaryNet n k) :
    p ∈ frontier (accumulatingDisk n) :=
  (Classical.choose_spec (exists_finite_disk_boundary_net n k)).1 p hp

def exteriorCenterNet (n k : ℕ) : Finset Coord := by
  classical
  exact (diskBoundaryNet n k).image (exteriorMiddleLift n k)

theorem exteriorCenterNet_mem_layer (n k : ℕ) {p : Coord} (hp : p ∈ exteriorCenterNet n k) :
    p ∈ exteriorOpenLayer n k := by
  classical
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  exact exteriorMiddleLift_mem_layer n k (diskBoundaryNet_mem_frontier n k hq)

theorem exteriorClosedLayer_disjoint_every_disk (n k m : ℕ) :
    Disjoint (exteriorClosedLayer n k) (accumulatingDisk m) := by
  by_cases hnm : n = m
  · subst m
    exact exteriorClosedLayer_outside_disk n k
  · exact (enlargedAccumulatingDisks_pairwise_disjoint hnm).mono
      (exteriorClosedLayer_subset_enlarged n k) (accumulatingDisk_subset_enlarged m)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_OrientationNet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Matrix BigOperators
open Set Metric

namespace SmoothLocal.Geometry

abbrev PlanarAxis := EuclideanSpace ℝ (Fin 2)

def axisRotation (a : PlanarAxis) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![a 1, a 0], ![-a 0, a 1]]

theorem planarAxis_sq_sum {a : PlanarAxis} (ha : ‖a‖ = 1) : a 0 ^ 2 + a 1 ^ 2 = 1 := by
  have h := EuclideanSpace.real_norm_sq_eq a
  rw [ha, one_pow, Fin.sum_univ_two] at h
  exact h.symm

theorem axisRotation_transpose_mul {a : PlanarAxis} (ha : ‖a‖ = 1) :
    (axisRotation a)ᵀ * axisRotation a = 1 := by
  have hs := planarAxis_sq_sum ha
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [axisRotation] <;> nlinarith [hs]

theorem axisRotation_mul_transpose {a : PlanarAxis} (ha : ‖a‖ = 1) :
    axisRotation a * (axisRotation a)ᵀ = 1 := by
  have hs := planarAxis_sq_sum ha
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [axisRotation] <;> nlinarith [hs]

theorem axisRotation_det {a : PlanarAxis} (ha : ‖a‖ = 1) : (axisRotation a).det = 1 := by
  have hs := planarAxis_sq_sum ha
  rw [Matrix.det_fin_two]
  simp [axisRotation]
  nlinarith [hs]

theorem exists_finite_unit_axis_net :
    ∃ axes : Finset PlanarAxis, (∀ a ∈ axes, ‖a‖ = 1) ∧
      ∀ v : PlanarAxis, ‖v‖ = 1 → ∃ a ∈ axes, dist v a < (1 / 1000 : ℝ) := by
  classical
  obtain ⟨s, hsphere, hsfinite, hcover⟩ :=
    (isCompact_sphere (0 : PlanarAxis) 1).finite_cover_balls
      (show (0 : ℝ) < 1 / 1000 by norm_num)
  refine ⟨hsfinite.toFinset, ?_, ?_⟩
  · intro a ha
    have hmem := hsphere (hsfinite.mem_toFinset.mp ha)
    simpa only [Metric.mem_sphere, dist_zero_right] using hmem
  · intro v hv
    have hvs : v ∈ sphere (0 : PlanarAxis) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hv
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hcover hvs)
    obtain ⟨has, hva⟩ := Set.mem_iUnion.mp ha
    exact ⟨a, hsfinite.mem_toFinset.mpr has, hva⟩

def orientationAxes : Finset PlanarAxis := Classical.choose exists_finite_unit_axis_net

theorem orientationAxes_unit (a : PlanarAxis) (ha : a ∈ orientationAxes) : ‖a‖ = 1 :=
  (Classical.choose_spec exists_finite_unit_axis_net).1 a ha

def orientationRotations : Finset (Matrix (Fin 2) (Fin 2) ℝ) := by
  classical
  exact orientationAxes.image axisRotation

theorem orientationRotations_properties {R : Matrix (Fin 2) (Fin 2) ℝ}
    (hR : R ∈ orientationRotations) : Rᵀ * R = 1 ∧ R * Rᵀ = 1 ∧ R.det = 1 := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hR
  exact ⟨axisRotation_transpose_mul (orientationAxes_unit a ha),
    axisRotation_mul_transpose (orientationAxes_unit a ha),
    axisRotation_det (orientationAxes_unit a ha)⟩

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_OrientedCenterNets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

abbrev OrientationLabel := {R : Matrix (Fin 2) (Fin 2) ℝ // R ∈ orientationRotations}

def orientationLabelCode (R : OrientationLabel) : ℕ :=
  (Fintype.equivFin OrientationLabel R).val

theorem orientationLabelCode_injective : Function.Injective orientationLabelCode := by
  intro R S h
  apply (Fintype.equivFin OrientationLabel).injective
  exact Fin.ext h

def orientedLayerIndex (k : ℕ) (R : OrientationLabel) : ℕ :=
  Nat.pair k (orientationLabelCode R)

theorem orientedLayerIndex_injective :
    Function.Injective (fun a : ℕ × OrientationLabel => orientedLayerIndex a.1 a.2) := by
  intro a b h
  have hab := Nat.pair_eq_pair.mp h
  exact Prod.ext hab.1 (orientationLabelCode_injective hab.2)

def orientedExteriorCenters (n k : ℕ) (R : OrientationLabel) : Finset Coord :=
  exteriorCenterNet n (orientedLayerIndex k R)

theorem orientedExteriorCenters_mem_layer (n k : ℕ) (R : OrientationLabel)
    {p : Coord} (hp : p ∈ orientedExteriorCenters n k R) :
    p ∈ exteriorOpenLayer n (orientedLayerIndex k R) :=
  exteriorCenterNet_mem_layer n (orientedLayerIndex k R) hp

theorem orientedExteriorLayers_disjoint (n : ℕ) {a b : ℕ × OrientationLabel} (hab : a ≠ b) :
    Disjoint (exteriorClosedLayer n (orientedLayerIndex a.1 a.2))
      (exteriorClosedLayer n (orientedLayerIndex b.1 b.2)) :=
  exteriorClosedLayers_pairwise_disjoint n (fun h => hab (orientedLayerIndex_injective h))

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_AffinePatchSquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

theorem finite_positive_lower_bound {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) : ∃ δ > 0, ∀ i ∈ s, δ < a i := by
  classical
  revert ha
  induction s using Finset.induction_on with
  | empty => intro ha; exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
      intro ha
      obtain ⟨δ, hδ, hδa⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have hai := ha i (Finset.mem_insert_self i s)
      refine ⟨min (a i / 2) δ, lt_min (by positivity) hδ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · exact lt_of_le_of_lt (min_le_right _ _) (hδa j hj)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_DiskCurvatureProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set

namespace SmoothLocal.Geometry

theorem roundRadiusSq_contDiff (c : Coord) : ContDiff ℝ ∞ (roundRadiusSq c) :=
  (((contDiff_apply ℝ ℝ 0).sub contDiff_const).pow 2).add
    (((contDiff_apply ℝ ℝ 1).sub contDiff_const).pow 2)

def negativeDiskProfile (c : Coord) (r : ℝ) (p : Coord) : ℝ :=
  -expNegInvGlue (r ^ 2 - roundRadiusSq c p)

theorem negativeDiskProfile_contDiff (c : Coord) (r : ℝ) :
    ContDiff ℝ ∞ (negativeDiskProfile c r) :=
  (expNegInvGlue.contDiff.comp (contDiff_const.sub (roundRadiusSq_contDiff c))).neg

theorem negativeDiskProfile_neg_inside (c : Coord) (r : ℝ) {p : Coord}
    (hp : p ∈ roundOpenDisk c r) : negativeDiskProfile c r p < 0 :=
  neg_neg_of_pos (expNegInvGlue.pos_of_pos (sub_pos.mpr hp))

theorem negativeDiskProfile_zero_outside (c : Coord) (r : ℝ) {p : Coord}
    (hp : p ∉ roundOpenDisk c r) : negativeDiskProfile c r p = 0 := by
  have hle : r ^ 2 ≤ roundRadiusSq c p := le_of_not_gt hp
  simp only [negativeDiskProfile, expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr hle), neg_zero]

theorem negativeDiskProfile_support (c : Coord) (r : ℝ) :
    Function.support (negativeDiskProfile c r) = roundOpenDisk c r := by
  ext p
  constructor
  · intro hp
    by_contra hnot
    exact hp (negativeDiskProfile_zero_outside c r hnot)
  · intro hp
    exact (negativeDiskProfile_neg_inside c r hp).ne

theorem negativeDiskProfile_tsupport_subset (c : Coord) {r : ℝ} (hr : 0 < r) :
    tsupport (negativeDiskProfile c r) ⊆ roundClosedDisk c r := by
  apply closure_minimal _ (isCompact_roundClosedDisk c hr).isClosed
  rw [negativeDiskProfile_support]
  exact fun p hp => (show roundRadiusSq c p < r^2 from hp).le

theorem negativeDiskProfile_hasCompactSupport (c : Coord) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (negativeDiskProfile c r) :=
  (isCompact_roundClosedDisk c hr).of_isClosed_subset (isClosed_tsupport _)
    (negativeDiskProfile_tsupport_subset c hr)

def accumulatingDiskProfile (n : ℕ) : Coord → ℝ :=
  negativeDiskProfile (accumulatingCenter n) (accumulatingRadius n)

theorem accumulatingDiskProfile_contDiff (n : ℕ) : ContDiff ℝ ∞ (accumulatingDiskProfile n) :=
  negativeDiskProfile_contDiff _ _

theorem accumulatingDiskProfile_tsupport_subset (n : ℕ) :
    tsupport (accumulatingDiskProfile n) ⊆ accumulatingDisk n :=
  negativeDiskProfile_tsupport_subset _ (accumulatingRadius_pos n)

theorem accumulatingDiskProfile_hasCompactSupport (n : ℕ) :
    HasCompactSupport (accumulatingDiskProfile n) :=
  negativeDiskProfile_hasCompactSupport _ (accumulatingRadius_pos n)

end SmoothLocal.Geometry

end

end OAI
end

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

def patchAxisCutoff (x : ℝ) : ℝ :=
  intervalCutoff (-(15 / 4 : ℝ)) (-(13 / 4 : ℝ)) x *
    intervalCutoff (-(15 / 4 : ℝ)) (-(13 / 4 : ℝ)) (-x)

theorem patchAxisCutoff_contDiff : ContDiff ℝ ∞ patchAxisCutoff :=
  (intervalCutoff_contDiff _ _).mul ((intervalCutoff_contDiff _ _).comp contDiff_id.neg)

theorem patchAxisCutoff_one {x : ℝ} (hx : |x| ≤ 13 / 4) : patchAxisCutoff x = 1 := by
  have hlo := (abs_le.mp hx).1
  have hhi := (abs_le.mp hx).2
  rw [patchAxisCutoff, intervalCutoff_one (by norm_num) hlo,
    intervalCutoff_one (by norm_num) (show -(13 / 4 : ℝ) ≤ -x by linarith)]
  norm_num

theorem patchAxisCutoff_zero_left {x : ℝ} (hx : x ≤ -(15 / 4 : ℝ)) :
    patchAxisCutoff x = 0 := by
  simp only [patchAxisCutoff, intervalCutoff_zero (b := -(13 / 4 : ℝ))
    (by norm_num) hx, zero_mul]

theorem patchAxisCutoff_zero_right {x : ℝ} (hx : 15 / 4 ≤ x) :
    patchAxisCutoff x = 0 := by
  simp only [patchAxisCutoff, intervalCutoff_zero (b := -(13 / 4 : ℝ)) (by norm_num)
    (show -x ≤ -(15 / 4 : ℝ) by linarith), mul_zero]

theorem patchAxisCutoff_support_bound {x : ℝ} (hx : patchAxisCutoff x ≠ 0) :
    |x| < 15 / 4 := by
  apply abs_lt.mpr
  constructor
  · by_contra h
    exact hx (patchAxisCutoff_zero_left (le_of_not_gt h))
  · by_contra h
    exact hx (patchAxisCutoff_zero_right (le_of_not_gt h))

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_InitialCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter

namespace SmoothLocal.Geometry
open SmoothLocal.Model

def initialCurvatureBudget : ℝ := 1 / 2000

theorem initialCurvatureBudget_pos : 0 < initialCurvatureBudget := by
  norm_num [initialCurvatureBudget]

end SmoothLocal.Geometry

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

theorem interval_product_abs_le_sqrt_squares
    {f g : ℝ → ℝ} {xl xr : ℝ} (hlr : xl ≤ xr)
    (hf : ContinuousOn f (Icc xl xr)) (hg : ContinuousOn g (Icc xl xr)) :
    |∫ x in xl..xr, f x * g x| ≤
      Real.sqrt (∫ x in xl..xr, f x ^ 2) * Real.sqrt (∫ x in xl..xr, g x ^ 2) := by
  have hf2 : MemLp f 2 (volume.restrict (Icc xl xr)) :=
    (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable measurableSet_Icc)).2
      ((hf.pow 2).integrableOn_compact isCompact_Icc)
  have hg2 : MemLp g 2 (volume.restrict (Icc xl xr)) :=
    (memLp_two_iff_integrable_sq (hg.aestronglyMeasurable measurableSet_Icc)).2
      ((hg.pow 2).integrableOn_compact isCompact_Icc)
  simpa only [intervalIntegral.integral_of_le hlr, restrict_Ioc_eq_restrict_Icc] using
    integral_product_abs_le_sqrt_squares hf2 hg2

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

theorem regularized_sqrt_rate_le
    {E Ed force C eta : ℝ} (hE : 0 ≤ E) (hforce : 0 ≤ force) (hC : 0 ≤ C)
    (heta : 0 < eta) (hEd : Ed ≤ C * E + Real.sqrt (2 * E) * force) :
    Ed / (2 * Real.sqrt (E + eta)) ≤ C * Real.sqrt (E + eta) + force := by
  have hpos : 0 < E + eta := by linarith
  have hrootpos := Real.sqrt_pos.2 hpos
  have hsquare := Real.sq_sqrt hpos.le
  have hroot : Real.sqrt (2 * E) ≤ 2 * Real.sqrt (E + eta) := by
    apply Real.sqrt_le_iff.2
    constructor
    · positivity
    · nlinarith
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (E + eta))).2
  have hf := mul_le_mul_of_nonneg_right hroot hforce
  have hCE : C * E ≤ 2 * C * (E + eta) := by
    nlinarith [mul_nonneg hC hE, mul_nonneg hC heta.le]
  nlinarith

def regularizedWeightedEnergy (E : ℝ → ℝ) (C a eta : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-C * (t - a)) * Real.sqrt (E t + eta)

def regularizedWeightedRate (E Ed : ℝ → ℝ) (C a eta : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-C * (t - a)) *
    (Ed t / (2 * Real.sqrt (E t + eta)) - C * Real.sqrt (E t + eta))

theorem regularizedWeightedEnergy_hasDerivAt
    {E : ℝ → ℝ} {Ed C a eta t : ℝ} (hd : HasDerivAt E Ed t)
    (hE : 0 ≤ E t) (heta : 0 < eta) :
    HasDerivAt (regularizedWeightedEnergy E C a eta)
      (Real.exp (-C * (t - a)) *
        (Ed / (2 * Real.sqrt (E t + eta)) - C * Real.sqrt (E t + eta))) t := by
  have hroot := (hd.add_const eta).sqrt (by linarith : E t + eta ≠ 0)
  have he := (((hasDerivAt_id t).sub_const a).const_mul (-C)).exp
  have hh := he.mul hroot
  simp only [id_eq, mul_one] at hh
  unfold regularizedWeightedEnergy
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MovingEnergyPropagation
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

theorem inward_interval_geometry
    {xl xr a b speed radius t : ℝ} (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hxl : -radius < xl) (hxr : xr < radius)
    (hlength : 2 * speed * (b - a) < xr - xl) (ht : t ∈ Icc a b) :
    inwardLeft xl a speed t ∈ Ioo (-radius) radius ∧
    inwardRight xr a speed t ∈ Ioo (-radius) radius ∧
    inwardLeft xl a speed t < inwardRight xr a speed t ∧
    0 < xr - xl - 2 * speed * (b - a) ∧
    xr - xl - 2 * speed * (b - a) ≤
      inwardRight xr a speed t - inwardLeft xl a speed t := by
  have hinc : 0 ≤ speed * (t - a) := mul_nonneg hspeed (sub_nonneg.mpr ht.1)
  have hmax := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hspeed
  have hspan : 0 ≤ speed * (b - a) := mul_nonneg hspeed (sub_nonneg.mpr hab)
  have hupper : speed * (t - a) < xr - xl := by
    linarith only [hmax, hspan, hlength]
  unfold inwardLeft inwardRight
  constructor
  · constructor
    · linarith
    · linarith only [hupper, hxr]
  constructor
  · constructor <;> linarith
  constructor
  · linarith
  constructor <;> linarith

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

def shrinkingSlab (xl xr a b speed : ℝ) : Set Coord :=
  {p | p 1 ∈ Icc a b ∧ p 0 ∈ Icc (inwardLeft xl a speed (p 1))
    (inwardRight xr a speed (p 1))}

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
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

def spatialLowFactorBound (lengthFloor : ℝ) (H : ℝ≥0) : ℝ :=
  max 1 (Real.sqrt (2 + 1 / lengthFloor) * (H : ℝ))

def spatialProductL2Budget (lengthFloor left right : ℝ) (H : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  ‖spatialLowFactorBound lengthFloor H ^ n‖ₑ *
    ((H : ℝ≥0∞) + (volume (Icc left right)) ^ (1 / (2 : ℝ)))

end SmoothLocal.Hyperbolic

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

def qFirstJetOffset : Fin 6 → ℕ := ![0, 0, 0, 0, 1, 1]

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
open SmoothLocal.Hyperbolic

def qPairSliceBudget (Cfirst : ℝ) (H : ℝ≥0) : ℝ≥0∞ :=
  ‖Cfirst‖ₑ * (H : ℝ≥0∞) + ‖Cfirst‖ₑ * (H : ℝ≥0∞)

end SmoothLocal.HighEquation

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

theorem real_near_closed_interval {a b e x : ℝ} (hab : a ≤ b)
    (he : 0 < e) (hx : x ∈ Ioo (a-e) (b+e)) :
    ∃ y ∈ Icc a b, |x-y| < e := by
  by_cases hxa : x < a
  · refine ⟨a,⟨le_rfl,hab⟩,?_⟩
    rw [abs_of_neg (sub_neg.mpr hxa)]
    linarith [hx.1]
  by_cases hbx : b < x
  · refine ⟨b,⟨hab,le_rfl⟩,?_⟩
    rw [abs_of_pos (sub_pos.mpr hbx)]
    linarith [hx.2]
  exact ⟨x,⟨le_of_not_gt hxa,le_of_not_gt hbx⟩,by simpa using he⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_BoundedHeightClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

def boundedClassSpeed (kappa : ℝ) (M : ℕ) : ℝ :=
  Real.sqrt (kappa / 2) * (M : ℝ) ^ (-(3 : ℝ) / 2)

def boundedClassWidth (kappa : ℝ) (M : ℕ) : ℝ :=
  100 * (1 + (boundedClassSpeed kappa M)⁻¹)

theorem boundedClassSpeed_pos {kappa : ℝ} (hkappa : 0 < kappa) {M : ℕ} (hM : 0 < M) :
    0 < boundedClassSpeed kappa M :=
  mul_pos (Real.sqrt_pos.mpr (div_pos hkappa (by norm_num)))
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hM) _)

theorem boundedClassWidth_ge_hundred (kappa : ℝ) (M : ℕ) :
    100 ≤ boundedClassWidth kappa M := by
  have hv : 0 ≤ boundedClassSpeed kappa M :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg M) _)
  have hi := inv_nonneg.mpr hv
  dsimp only [boundedClassWidth]
  linarith

theorem boundedClassWidth_pos (kappa : ℝ) (M : ℕ) :
    0 < boundedClassWidth kappa M :=
  (by norm_num : (0 : ℝ) < 100).trans_le (boundedClassWidth_ge_hundred kappa M)

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QPositiveFloor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix BigOperators

namespace SmoothLocal.Geometry

def pointHessianBound (G Z d : ℝ) : ℝ := Z + 6 * (G / d) * G * Z

theorem pointHessianBound_nonneg {G Z d : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) : 0 ≤ pointHessianBound G Z d := by
  unfold pointHessianBound
  positivity

end SmoothLocal.Geometry

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Flow

def shearedHessianUpper (G Z d q0 : ℝ) : ℝ :=
  1 + (1 + |q0|)^2 * pointHessianBound G Z d

def shearedQPositiveFloor (G Z d q0 M : ℝ) : ℝ :=
  1 / (M * shearedHessianUpper G Z d q0)

theorem shearedHessianUpper_pos {G Z d : ℝ} (q0 : ℝ)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) : 0 < shearedHessianUpper G Z d q0 := by
  have hH := pointHessianBound_nonneg hG hZ hd
  unfold shearedHessianUpper
  positivity

theorem shearedQPositiveFloor_pos {G Z d M : ℝ} (q0 : ℝ)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hM : 0 < M) :
    0 < shearedQPositiveFloor G Z d q0 M :=
  one_div_pos.mpr (mul_pos hM (shearedHessianUpper_pos q0 hG hZ hd))

theorem positive_negative_ratio_floor {a b M H : ℝ}
    (hM : 0 < M) (hH : 0 < H) (hb : b ≠ 0)
    (hpos : 0 < -(a / b)) (ha : 1 / M ≤ |a|) (hupper : |b| ≤ H) :
    1 / (M * H) ≤ -(a / b) := by
  have hratio : -(a / b) = |a| / |b| := by
    rw [← abs_of_pos hpos, abs_neg, abs_div]
  rw [hratio]
  calc
    1 / (M * H) = (1 / M) / H := by rw [div_div]
    _ ≤ |a| / H := div_le_div_of_nonneg_right ha hH.le
    _ ≤ |a| / |b| := div_le_div_of_nonneg_left
      ((one_div_pos.mpr hM).le.trans ha) (abs_pos.mpr hb) hupper

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_BoundedClassHyperbolicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation

theorem boundedClassSpeed_sq {kappa : ℝ} (hkappa : 0 < kappa)
    {M : ℕ} (hM : 0 < M) :
    (boundedClassSpeed kappa M) ^ 2 = kappa / (2 * (M : ℝ) ^ 3) := by
  have hMp : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have he : ((M : ℝ) ^ (-(3 : ℝ) / 2)) ^ (2 : ℕ) = ((M : ℝ) ^ (3 : ℕ))⁻¹ := by
    rw [← Real.rpow_mul_natCast hMp.le]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  unfold boundedClassSpeed
  rw [mul_pow, Real.sq_sqrt (by positivity), he]
  ring

theorem boundedClassSpeed_sq_energy {kappa : ℝ} (hkappa : 0 < kappa)
    {M : ℕ} (hM : 0 < M) :
    (boundedClassSpeed kappa M) ^ 2 =
      kappa * (1 / (M : ℝ)) / (2 * (M : ℝ) ^ 2) := by
  rw [boundedClassSpeed_sq hkappa hM]
  field_simp

theorem boundedClassShearHxxFloor_pos {kappa : ℝ} (hkappa : 0 < kappa)
    {M : ℕ} (hM : 0 < M) :
    0 < (boundedClassSpeed kappa M) ^ 2 / (2 * (M : ℝ)) :=
  div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
    (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_RankOneOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Matrix BigOperators
open WithLp

namespace SmoothLocal.Geometry

def clockwiseAxis (a : PlanarAxis) : PlanarAxis := toLp 2 ![a 1, -a 0]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_LocalDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function TopologicalSpace
open scoped ContDiff Topology Manifold Matrix

namespace SmoothLocal.Geometry

section Extension
variable {E : Type*}

def openDomainExtend (U : Opens Coord) (F : U → E) (outside : E) : Coord → E :=
  Function.extend Subtype.val F (fun _ => outside)

@[simp] theorem openDomainExtend_apply (U : Opens Coord) (F : U → E)
    (outside : E) (p : U) : openDomainExtend U F outside p = F p :=
  Subtype.val_injective.extend_apply F (fun _ => outside) p

end Extension

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_FiniteOscillatoryMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse

theorem compact_weight_cos_phase_step {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {tau : ℝ} (htau : 0 < tau) (phase : ℝ) :
    (∫ x : ℝ, f x*Real.cos (tau*x+phase)) =
      -(∫ x : ℝ, deriv f x*Real.cos (tau*x+(phase-Real.pi/2)))/tau := by
  let v : ℝ → ℝ := fun x => Real.sin (tau*x+phase)/tau
  have hc : Continuous (fun x : ℝ => Real.cos (tau*x+phase)) := by fun_prop
  have hvcont : Continuous v := by dsimp only [v]; fun_prop
  have hdcont : Continuous (deriv f) := (contDiff_infty_iff_deriv.mp hf).2.continuous
  have hdcompact : HasCompactSupport (deriv f) := hcompact.deriv
  have hfc : Integrable (fun x : ℝ => f x*Real.cos (tau*x+phase)) :=
    (hf.continuous.mul hc).integrable_of_hasCompactSupport hcompact.mul_right
  have hdfv : Integrable (fun x : ℝ => deriv f x*v x) :=
    (hdcont.mul hvcont).integrable_of_hasCompactSupport hdcompact.mul_right
  have hfv : Integrable (fun x : ℝ => f x*v x) :=
    (hf.continuous.mul hvcont).integrable_of_hasCompactSupport hcompact.mul_right
  have hv (x : ℝ) : HasDerivAt v (Real.cos (tau*x+phase)) x := by
    have h := ((Real.hasDerivAt_sin (tau*x+phase)).comp x
      (((hasDerivAt_id x).const_mul tau).add_const phase)).div_const tau
    simp only [id_eq,Function.comp_def] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    field_simp [htau.ne']
  have hibp : (∫ x : ℝ, f x*Real.cos (tau*x+phase)) = -∫ x : ℝ, deriv f x*v x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
      (fun x _ => hv x) hfc hdfv hfv
  have heq : (fun x : ℝ => deriv f x*v x) =
      fun x => (deriv f x*Real.cos (tau*x+(phase-Real.pi/2)))/tau := by
    funext x
    have hp : tau*x+(phase-Real.pi/2) = (tau*x+phase)-Real.pi/2 := by ring
    rw [hp,Real.cos_sub_pi_div_two]
    dsimp only [v]
    ring
  rw [hibp,heq,integral_div]
  ring

theorem compact_weight_cos_phase_order_le (N : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {tau : ℝ} (htau : 0 < tau) (phase : ℝ) :
    |∫ x : ℝ, f x*Real.cos (tau*x+phase)| ≤
      (∫ x : ℝ, |iteratedDeriv N f x|)/tau^N := by
  induction N generalizing f phase with
  | zero =>
      have hi : Integrable (fun x : ℝ => |f x|) :=
        hf.continuous.abs.integrable_of_hasCompactSupport hcompact.abs
      have hnorm : ∀ x : ℝ, ‖f x*Real.cos (tau*x+phase)‖ ≤ |f x| := by
        intro x
        simp only [Real.norm_eq_abs,abs_mul]
        exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _)
      simpa only [iteratedDeriv_zero,pow_zero,div_one,Real.norm_eq_abs] using
        norm_integral_le_of_norm_le hi (Eventually.of_forall hnorm)
  | succ N ih =>
      have hdf : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
      have hnext := ih hdf hcompact.deriv (phase-Real.pi/2)
      rw [compact_weight_cos_phase_step hf hcompact htau phase,abs_div,abs_neg,abs_of_pos htau]
      calc
        _ ≤ ((∫ x : ℝ, |iteratedDeriv N (deriv f) x|)/tau^N)/tau :=
          div_le_div_of_nonneg_right hnext htau.le
        _ = _ := by rw [iteratedDeriv_succ',pow_succ]; field_simp [htau.ne']

theorem compact_weight_cos_order_le (N : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {tau : ℝ} (htau : 0 < tau) :
    |∫ x : ℝ, f x*Real.cos (tau*x)| ≤ (∫ x : ℝ, |iteratedDeriv N f x|)/tau^N := by
  simpa only [add_zero] using compact_weight_cos_phase_order_le N hf hcompact htau 0

theorem finite_oscillatory_weight_bound (N : ℕ) {f : ℝ → ℝ} {B tau : ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f) (htau : 0 < tau)
    (hB : (∫ x : ℝ, |iteratedDeriv N f x|) ≤ B) :
    |∫ x : ℝ, f x*Real.cos (tau*x)| ≤ B/tau^N :=
  (compact_weight_cos_order_le N hf hcompact htau).trans
    (div_le_div_of_nonneg_right hB (pow_nonneg htau.le N))

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_CutoffEdgeMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse

def cutoffEdgeWeight (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := axisBump a x*f x

theorem cutoffEdgeWeight_contDiff {a : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I) (hsub : Icc (-a) a ⊆ I) :
    ContDiff ℝ ∞ (cutoffEdgeWeight a f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ I
  · exact (axisBump_contDiff a).contDiffAt.mul (hf.contDiffAt (hI.mem_nhds hx))
  · have hnot : x ∉ tsupport (axisBump a) := fun ht => hx (hsub (axisBump_tsupport_subset ha ht))
    have hzero := notMem_tsupport_iff_eventuallyEq.mp hnot
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    change axisBump a y*f y = 0
    change axisBump a y = (0 : ℝ) at hy
    rw [hy,zero_mul]

theorem cutoffEdgeWeight_hasCompactSupport {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    HasCompactSupport (cutoffEdgeWeight a f) := (axisBump_hasCompactSupport ha).mul_right

theorem iteratedDeriv_tsupport_subset (N : ℕ) (f : ℝ → ℝ) :
    tsupport (iteratedDeriv N f) ⊆ tsupport f := by
  induction N with
  | zero => simp only [iteratedDeriv_zero,subset_refl]
  | succ N ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

theorem cutoffEdgeWeight_iteratedDeriv_zero_off {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ)
    (N : ℕ) {x : ℝ} (hx : x ∉ Icc (-a) a) :
    iteratedDeriv N (cutoffEdgeWeight a f) x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact hx (axisBump_tsupport_subset ha (tsupport_mul_subset_left
    (iteratedDeriv_tsupport_subset N (cutoffEdgeWeight a f) hmem)))

def cutoffEdgeDerivativeBound (a : ℝ) (ha : 0 < a) (N : ℕ) (B : ℝ) : ℝ :=
  derivativeConvolution (axisBumpDerivativeBound a ha) (fun _ => B) N

theorem cutoffEdgeWeight_iteratedDeriv_bound {a B : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I)
    (hsub : Icc (-a) a ⊆ I) (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a, ‖iteratedFDeriv ℝ k f x‖ ≤ B)
    {x : ℝ} (hx : x ∈ Icc (-a) a) :
    |iteratedDeriv N (cutoffEdgeWeight a f) x| ≤ cutoffEdgeDerivativeBound a ha N B := by
  have hχ : ContDiffAt ℝ N (axisBump a) x := (axisBump_contDiff a).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfx : ContDiffAt ℝ N f x := (hf.contDiffAt (hI.mem_nhds (hsub hx))).of_le (WithTop.coe_le_coe.mpr le_top)
  have hprod := iteratedDeriv_mul hχ hfx
  change iteratedDeriv N (cutoffEdgeWeight a f) x = _ at hprod
  rw [←Real.norm_eq_abs,hprod]
  refine (norm_sum_le _ _).trans ?_
  unfold cutoffEdgeDerivativeBound derivativeConvolution
  apply Finset.sum_le_sum
  intro index _
  have hχb : ‖iteratedDeriv index (axisBump a) x‖ ≤ axisBumpDerivativeBound a ha index := by
    rw [←norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact axisBump_derivative_le ha index x
  have hfb : ‖iteratedDeriv (N-index) f x‖ ≤ B := by
    rw [←norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hjet (N-index) (Nat.sub_le _ _) x hx
  simp only [norm_mul,Real.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hfb
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hχb (Nat.cast_nonneg _)) hB)

theorem cutoffEdgeWeight_iteratedDeriv_L1 {a B : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I)
    (hsub : Icc (-a) a ⊆ I) (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a, ‖iteratedFDeriv ℝ k f x‖ ≤ B) :
    (∫ x : ℝ, |iteratedDeriv N (cutoffEdgeWeight a f) x|) ≤
      (2*a)*cutoffEdgeDerivativeBound a ha N B := by
  have hglobal := cutoffEdgeWeight_contDiff ha hI hf hsub
  have hcont : Continuous (fun x => |iteratedDeriv N (cutoffEdgeWeight a f) x|) :=
    (hglobal.continuous_iteratedDeriv N (WithTop.coe_le_coe.mpr le_top)).abs
  have hrestrict : (∫ x in Icc (-a) a, |iteratedDeriv N (cutoffEdgeWeight a f) x|) =
      ∫ x : ℝ, |iteratedDeriv N (cutoffEdgeWeight a f) x| := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [cutoffEdgeWeight_iteratedDeriv_zero_off ha f N hx,abs_zero]
  rw [←hrestrict]
  have hm := integral_mono_ae (μ := volume.restrict (Icc (-a) a)) hcont.continuousOn.integrableOn_Icc
    ((continuous_const : Continuous (fun _ : ℝ => cutoffEdgeDerivativeBound a ha N B)).continuousOn.integrableOn_Icc)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact cutoffEdgeWeight_iteratedDeriv_bound ha hB hI hf hsub N hjet hx)
  rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith : -a ≤ a),smul_eq_mul] at hm
  simpa only [sub_neg_eq_add,two_mul] using hm

theorem cutoffEdgeWeight_cos_integral_bound {a B tau : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (htau : 0 < tau)
    (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I) (hsub : Icc (-a) a ⊆ I) (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a, ‖iteratedFDeriv ℝ k f x‖ ≤ B) :
    |∫ x : ℝ, axisBump a x*f x*Real.cos (tau*x)| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N :=
  finite_oscillatory_weight_bound N (cutoffEdgeWeight_contDiff ha hI hf hsub)
    (cutoffEdgeWeight_hasCompactSupport ha f) htau
    (cutoffEdgeWeight_iteratedDeriv_L1 ha hB hI hf hsub N hjet)

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

def pulsePairRectangle (a delta tau : ℝ) : Set (ℝ × ℝ) :=
  Icc (-(delta/tau)) (delta/tau) ×ˢ Icc (-a) a
def pulseTest (a tau x : ℝ) : ℝ := axisBump a x*Real.cos (tau*x)

theorem pulsePairRectangle_isCompact (a delta tau : ℝ) :
    IsCompact (pulsePairRectangle a delta tau) := isCompact_Icc.prod isCompact_Icc

theorem pulseTest_continuous (a tau : ℝ) : Continuous (pulseTest a tau) :=
  (axisBump_contDiff a).continuous.mul (by fun_prop)

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

theorem pulseTest_abs_le (a tau x : ℝ) : |pulseTest a tau x| ≤ axisBump a x := by
  unfold pulseTest
  rw [abs_mul,abs_of_nonneg (axisBump_nonneg a x)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (axisBump_nonneg a x)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseTestEnergy
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

theorem pulseTest_contDiff (a tau : ℝ) : ContDiff ℝ ∞ (pulseTest a tau) :=
  (axisBump_contDiff a).mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

theorem pulseTest_hasDerivAt (a tau x : ℝ) :
    HasDerivAt (pulseTest a tau)
      (deriv (axisBump a) x*Real.cos (tau*x)-tau*axisBump a x*Real.sin (tau*x)) x := by
  have hχ := ((axisBump_contDiff a).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasDerivAt
  have hc := (Real.hasDerivAt_cos (tau*x)).comp x ((hasDerivAt_id x).const_mul tau)
  have h := hχ.mul hc
  simp only [Function.comp_def,mul_one] at h
  convert h using 1 <;> (first | rfl | ring)

theorem pulseTest_deriv (a tau x : ℝ) :
    deriv (pulseTest a tau) x =
      deriv (axisBump a) x*Real.cos (tau*x)-tau*axisBump a x*Real.sin (tau*x) :=
  (pulseTest_hasDerivAt a tau x).deriv

def pulseTestDerivativeBound (a : ℝ) (ha : 0 < a) : ℝ :=
  axisBumpDerivativeBound a ha 1+axisBumpDerivativeBound a ha 0

theorem pulseTestDerivativeBound_nonneg {a : ℝ} (ha : 0 < a) :
    0 ≤ pulseTestDerivativeBound a ha :=
  add_nonneg (axisBumpDerivativeBound_pos ha 1).le (axisBumpDerivativeBound_pos ha 0).le

theorem pulseTest_deriv_bound {a tau : ℝ} (ha : 0 < a) (ht : 1 ≤ tau) (x : ℝ) :
    |deriv (pulseTest a tau) x| ≤ pulseTestDerivativeBound a ha*tau := by
  have hA0 := (axisBumpDerivativeBound_pos ha 0).le
  have hA1 := (axisBumpDerivativeBound_pos ha 1).le
  have hχ : |axisBump a x| ≤ axisBumpDerivativeBound a ha 0 := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using axisBump_derivative_le ha 0 x
  have hχ' : |deriv (axisBump a) x| ≤ axisBumpDerivativeBound a ha 1 := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_one,Real.norm_eq_abs]
      using axisBump_derivative_le ha 1 x
  have ht0 : 0 ≤ tau := zero_le_one.trans ht
  rw [pulseTest_deriv]
  calc
    _ ≤ |deriv (axisBump a) x*Real.cos (tau*x)|+
        |tau*axisBump a x*Real.sin (tau*x)| := abs_sub _ _
    _ ≤ axisBumpDerivativeBound a ha 1+tau*axisBumpDerivativeBound a ha 0 := by
      apply add_le_add
      · rw [abs_mul]
        simpa only [mul_one] using mul_le_mul hχ' (Real.abs_cos_le_one _) (abs_nonneg _) hA1
      · rw [abs_mul,abs_mul,abs_of_nonneg ht0]
        simpa only [mul_one] using mul_le_mul
          (mul_le_mul_of_nonneg_left hχ ht0) (Real.abs_sin_le_one _) (abs_nonneg _) (mul_nonneg ht0 hA0)
    _ ≤ _ := by
      unfold pulseTestDerivativeBound
      nlinarith [mul_le_mul_of_nonneg_left ht hA1]

theorem real_Icc_memLp_two {f : ℝ → ℝ} {l r : ℝ} (hf : ContinuousOn f (Icc l r)) :
    MemLp f 2 (volume.restrict (Icc l r)) :=
  (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable measurableSet_Icc)).mpr
    ((hf.pow 2).integrableOn_Icc)

theorem sqrt_Icc_square_le_of_abs {f : ℝ → ℝ} {l r F : ℝ}
    (hlr : l ≤ r) (hF : 0 ≤ F) (hf : ContinuousOn f (Icc l r))
    (hbound : ∀ x ∈ Icc l r, |f x| ≤ F) :
    Real.sqrt (∫ x in Icc l r, f x^2) ≤ F*Real.sqrt (r-l) := by
  have hsq : (∫ x in Icc l r, f x^2) ≤ F^2*(r-l) := by
    have hm := integral_mono_ae (μ := volume.restrict (Icc l r)) ((hf.pow 2).integrableOn_Icc)
      ((continuous_const : Continuous (fun _ : ℝ => F^2)).continuousOn.integrableOn_Icc) (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        have hh := (sq_le_sq₀ (abs_nonneg (f x)) hF).mpr (hbound x hx)
        simpa only [Pi.pow_apply,sq_abs] using hh)
    rw [setIntegral_const,Real.volume_real_Icc_of_le hlr,smul_eq_mul] at hm
    simpa only [Pi.pow_apply,mul_comm] using hm
  apply (Real.sqrt_le_sqrt hsq).trans_eq
  rw [Real.sqrt_mul (sq_nonneg F),Real.sqrt_sq_eq_abs,abs_of_nonneg hF]

theorem real_Icc_pairing_bound {f h : ℝ → ℝ} {l r F G : ℝ}
    (hlr : l ≤ r) (hF : 0 ≤ F) (hf : ContinuousOn f (Icc l r))
    (hh : ContinuousOn h (Icc l r)) (hbound : ∀ x ∈ Icc l r, |f x| ≤ F)
    (hL2 : Real.sqrt (∫ x in Icc l r, h x^2) ≤ G) :
    |∫ x in Icc l r, f x*h x| ≤ F*Real.sqrt (r-l)*G := by
  have hcs := integral_product_abs_le_sqrt_squares (real_Icc_memLp_two hf) (real_Icc_memLp_two hh)
  exact hcs.trans (mul_le_mul (sqrt_Icc_square_le_of_abs hlr hF hf hbound) hL2
    (Real.sqrt_nonneg _) (mul_nonneg hF (Real.sqrt_nonneg _)))

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
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem pulse_test_interval_eq_global {a : ℝ} (ha : 0 < a) (tau : ℝ) (f : ℝ → ℝ) :
    (∫ x in (-a)..a, pulseTest a tau x*f x) =
      ∫ x : ℝ, axisBump a x*f x*Real.cos (tau*x) := by
  rw [intervalIntegral.integral_of_le (by linarith : -a ≤ a),←integral_Icc_eq_integral_Ioc]
  calc
    _ = ∫ x in Icc (-a) a, axisBump a x*f x*Real.cos (tau*x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro _ _
      unfold pulseTest
      ring
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : axisBump a x = 0 := by
        by_contra hn
        have hs := abs_lt.mp (axisBump_support_bound ha hn)
        exact hx ⟨hs.1.le,hs.2.le⟩
      simp only [hz,zero_mul]

theorem pulse_test_interval_finite_bound {a B tau : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (htau : 0 < tau)
    (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I) (hsub : Icc (-a) a ⊆ I) (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a, ‖iteratedFDeriv ℝ k f x‖ ≤ B) :
    |∫ x in (-a)..a, pulseTest a tau x*f x| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N := by
  rw [pulse_test_interval_eq_global ha]
  exact cutoffEdgeWeight_cos_integral_bound ha hB htau hI hf hsub N hjet

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

def initialShearedStateBudget (Z q0 : ℝ) : ℝ :=
  max 1 ((2*(1+|q0|))^2*Z)

end SmoothLocal.Taylor

end

end OAI
end


