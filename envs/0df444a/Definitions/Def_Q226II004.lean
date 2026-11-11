-- Prove2me | Definitions.Def_Q226II004
-- name    : Q226II004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:38:18.319204+00:00
-- url     : https://prove2.me/theorems/83f34b73-df73-4355-b0a7-7ab0a2418ea7
-- title:
--   Definitions bundle Q226II004 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 332 declarations of OpenAI's Lean: 91 definitions, 2 instances and 239 theorems. The definitions and types are `OAI.SmoothLocal.Flow.capChartSigma`, `OAI.SmoothLocal.Flow.capModelCurvature`, `OAI.SmoothLocal.Flow.coordinateGradientSquare`, `OAI.SmoothLocal.Flow.driftOperator`, `OAI.SmoothLocal.Flow.heightOriginalA`, `OAI.SmoothLocal.Flow.heightOriginalB`, `OAI.SmoothLocal.Flow.heightOriginalC0`, `OAI.SmoothLocal.Flow.heightUniformCapEstimateRHS`, `OAI.SmoothLocal.Flow.initialSecondForcing`, `OAI.SmoothLocal.Flow.initialThirdForcing`, `OAI.SmoothLocal.Flow.mixedFlowDerivative`, `OAI.SmoothLocal.Geometry.AssemblyProfileIndex`, `OAI.SmoothLocal.Geometry.IsometricOn`, `OAI.SmoothLocal.Geometry.LocalIsometric`, `OAI.SmoothLocal.Geometry.PatchAddress`, `OAI.SmoothLocal.Geometry.affinePullbackImmersion`, `OAI.SmoothLocal.Geometry.affineTensorJetFactor`, `OAI.SmoothLocal.Geometry.affineTensorOrderFactor`, `OAI.SmoothLocal.Geometry.assemblyCarrier`, `OAI.SmoothLocal.Geometry.christoffelAlongD`, `OAI.SmoothLocal.Geometry.closedAffineSquare`, `OAI.SmoothLocal.Geometry.closedPatchBox`, `OAI.SmoothLocal.Geometry.connectionBracket`, `OAI.SmoothLocal.Geometry.connectionTraceY`, `OAI.SmoothLocal.Geometry.coordinateDrift`, `OAI.SmoothLocal.Geometry.covDerivHessian`, `OAI.SmoothLocal.Geometry.curvatureDriftError`, `OAI.SmoothLocal.Geometry.curvatureFactor`, `OAI.SmoothLocal.Geometry.darbouxG`, `OAI.SmoothLocal.Geometry.driftJ`, `OAI.SmoothLocal.Geometry.explicitDriftError`, `OAI.SmoothLocal.Geometry.localPatchProfile`, `OAI.SmoothLocal.Geometry.openPatchBox`, `OAI.SmoothLocal.Geometry.orientedClosedPatch`, `OAI.SmoothLocal.Geometry.orientedPatchScale`, `OAI.SmoothLocal.Geometry.patchAddressCarrier`, `OAI.SmoothLocal.Geometry.patchAddressCenter`, `OAI.SmoothLocal.Geometry.patchAddressMatrix`, `OAI.SmoothLocal.Geometry.patchBoxCutoff`, `OAI.SmoothLocal.Geometry.patchTensorAddress` and 51 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Assembly_AssemblyProfiles`, `IsometricImmersion_Assembly_EnumeratedPatchTensors`, `IsometricImmersion_Assembly_SupportedPerturbations`, `IsometricImmersion_Assembly_TensorSeriesLocality`, `IsometricImmersion_Calculus_AffineTensorJetBounds`, `IsometricImmersion_Calculus_ClosedSquareJetBounds`, `IsometricImmersion_Calculus_CoordinateJetBounds`, `IsometricImmersion_Calculus_CoordinateJetReverseNorm`, `IsometricImmersion_Calculus_HessianCommutator`, `IsometricImmersion_Calculus_HessianJetBounds`, `IsometricImmersion_Calculus_MetricInverseJetBounds`, `IsometricImmersion_Calculus_MetricTwoJet`, `IsometricImmersion_Calculus_MixedCoordinateCalculus`, `IsometricImmersion_Calculus_NormedCoordinateCalculus`, `IsometricImmersion_Calculus_QuotientCalculus`, `IsometricImmersion_Calculus_QuotientLowBounds`, `IsometricImmersion_Calculus_QuotientLowRecurrence`, `IsometricImmersion_Calculus_SecondJetExtraction`, `IsometricImmersion_Calculus_SmoothCurry`, `IsometricImmersion_Calculus_VerticalSliceJets`, `IsometricImmersion_Caps_CapAreaFormula`, `IsometricImmersion_Caps_CapFlowUniqueness`, `IsometricImmersion_Caps_CapGradientTransport`, `IsometricImmersion_Caps_CapInductionData`, `IsometricImmersion_Caps_CapInteriorEnergy`, `IsometricImmersion_Caps_CapJacobian`, `IsometricImmersion_Caps_CapL2Basics`, `IsometricImmersion_Caps_EllipticGradient`, `IsometricImmersion_Caps_EllipticRatio`, `IsometricImmersion_Caps_HeightCapLowData`, `IsometricImmersion_Caps_PhysicalCapTransport`, `IsometricImmersion_Caps_UniformOriginalDataCapEstimate`, `IsometricImmersion_Coordinates_AffinePatchSquares`, `IsometricImmersion_Coordinates_AffinePullback`, `IsometricImmersion_Coordinates_OrientedPatchSquares`, `IsometricImmersion_Curvature_CurvatureParameter`, `IsometricImmersion_Curvature_IntrinsicCurvature`, `IsometricImmersion_Curvature_PatchCurvatureProfiles`, `IsometricImmersion_Darboux_ActualDriftCoefficients`, `IsometricImmersion_Darboux_DarbouxJet`, `IsometricImmersion_Darboux_DriftBounds`, `IsometricImmersion_Darboux_MixedDarbouxElimination`, `IsometricImmersion_Darboux_ModelPrincipal`, `IsometricImmersion_Darboux_SixVariableDarboux`, `IsometricImmersion_Darboux_SixVariableLinearization`, `IsometricImmersion_Energy_ActualRemainderL2`, `IsometricImmersion_Energy_DirectedCoercivity`, `IsometricImmersion_Energy_DirectedFarNegative`, `IsometricImmersion_Energy_HeightEnergyJetBounds`, `IsometricImmersion_Energy_MixedDerivativeL2`, `IsometricImmersion_Energy_MixedRemainderL2`, `IsometricImmersion_Energy_WeightPrimitive`, `IsometricImmersion_Energy_WeightPrimitiveParameter`, `IsometricImmersion_Estimates_ActualRemainderFactors`, `IsometricImmersion_Estimates_ActualRemainderRegularity`, `IsometricImmersion_Estimates_LargestBlockLinearization`, `IsometricImmersion_Estimates_MixedRemainderFactors`, `IsometricImmersion_Estimates_RemainderAreaBudget`, `IsometricImmersion_Flows_FlowBounds`, `IsometricImmersion_Flows_FlowChart`, `IsometricImmersion_Flows_FlowCurvature`, `IsometricImmersion_Flows_FlowHeightCoefficients`, `IsometricImmersion_Flows_FlowInverse`, `IsometricImmersion_Flows_FlowLowBounds`, `IsometricImmersion_Flows_FlowSecondVariation`, `IsometricImmersion_Flows_FlowThirdVariation`, `IsometricImmersion_Flows_FlowTimeVariation`, `IsometricImmersion_Flows_FlowTransport`, `IsometricImmersion_Flows_FlowVariation`, `IsometricImmersion_Immersions_HeightCoefficientClosedBounds`, `IsometricImmersion_Immersions_HeightNumericParameters`, `IsometricImmersion_LocalDomains`, `IsometricImmersion_Metric`, `IsometricImmersion_Metrics_MetricCompatibility`, `IsometricImmersion_Metrics_MetricPBundleBounds`, `IsometricImmersion_Metrics_ModelCoercivity`, `IsometricImmersion_Metrics_RemainderCoefficientBounds`, `IsometricImmersion_Metrics_UniversalMetricP`, `IsometricImmersion_Taylor_ActualDarbouxFaa`, `IsometricImmersion_Taylor_ChainResidual`, `IsometricImmersion_Taylor_ChainTermDerivative`, `IsometricImmersion_Taylor_ScalarChainExpansion`, `IsometricImmersion_Taylor_TopChainExtraction`, `IsometricImmersion_Volterra_VolterraParameterJets`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II000` and `Q226II001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q226II007`, `Q226II008`, `Q226II009` and `Q226II010`.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 334; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
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
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_IsometricImmersion
import Definitions.Def_Q226II000
import Definitions.Def_Q226II001

section
-- module Solutions.Q226_II.IsometricImmersion_Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix ContDiff
namespace SmoothLocal.Geometry

def IsometricOn (g : MetricField) (F : Coord → Ambient) (U : Set Coord) : Prop :=
  ContDiffOn ℝ ∞ F U ∧ ∀ p ∈ U, ∀ v w : Coord,
    inner ℝ (fderiv ℝ F p v) (fderiv ℝ F p w) = v ⬝ᵥ (g p *ᵥ w)

end SmoothLocal.Geometry

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

def coordinateDrift (q w : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 w p - q p * coordPartial 1 w p

def explicitDriftError (h E T J : Coord → ℝ) (p : Coord) : ℝ :=
  E p / (h p) ^ 2 * (T p - coordPartial 1 h p / h p) + J p / h p

theorem explicitDriftError_contDiffOn
    {E T J : Coord → ℝ} (hU : IsOpen U)
    (hh : ContDiffOn ℝ ∞ h U) (hE : ContDiffOn ℝ ∞ E U)
    (hT : ContDiffOn ℝ ∞ T U) (hJ : ContDiffOn ℝ ∞ J U)
    (hne : ∀ p ∈ U, h p ≠ 0) :
    ContDiffOn ℝ ∞ (explicitDriftError h E T J) U := by
  have hG : ContDiffOn ℝ ∞ (fun p => E p / (h p) ^ 2) U :=
    hE.div (hh.pow 2) (fun p hp => pow_ne_zero 2 (hne p hp))
  have hhy : ContDiffOn ℝ ∞ (coordPartial 1 h) U :=
    partial_contDiffOn hh hU 1
  exact (hG.mul (hT.sub (hhy.div hh hne))).add (hJ.div hh hne)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_HessianCommutator
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace HessianCalculus

variable {f h : Coord → ℝ} {p : Coord}

theorem coordPartial_sub_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q - h q) p = coordPartial i f p - coordPartial i h p := by
  simp [coordPartial, fderiv_fun_sub hf hh]

end HessianCalculus

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

def covDerivHessian (g : MetricField) (z : Coord → ℝ)
    (i j k : Fin 2) (p : Coord) : ℝ :=
  coordPartial i (fun q => covHessian g z q j k) p -
    (∑ a, christoffel g a i j p * covHessian g z p a k) -
    (∑ a, christoffel g a i k p * covHessian g z p j a)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_AffinePullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def affinePullbackImmersion (F : Coord → Ambient) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) : Coord → Ambient :=
  F ∘ affineCoordinates b R

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_AffinePatchSquares
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

def closedPatchBox : Set Coord := {x | ∀ i, x i ∈ Set.Icc (-4 : ℝ) 4}

theorem mem_closedPatchBox_iff_norm_le (x : Coord) :
    x ∈ closedPatchBox ↔ ‖x‖ ≤ 4 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  simp only [closedPatchBox, Set.mem_ofPred_eq, Set.mem_Icc, Real.norm_eq_abs, abs_le]

def closedAffineSquare (c : Coord) (scale : ℝ) (R : Matrix (Fin 2) (Fin 2) ℝ) : Set Coord :=
  affineCoordinates c (scale • R) '' closedPatchBox

theorem closedAffineSquare_dist_le (c : Coord) {scale : ℝ} (hscale : 0 ≤ scale)
    (R : Matrix (Fin 2) (Fin 2) ℝ) {p : Coord} (hp : p ∈ closedAffineSquare c scale R) :
    dist p c ≤ scale * (4 * ‖matrixContinuousLinear R‖) := by
  obtain ⟨x, hx, rfl⟩ := hp
  have hxnorm := (mem_closedPatchBox_iff_norm_le x).mp hx
  have hmap := (matrixContinuousLinear R).le_opNorm_of_le hxnorm
  calc
    dist (affineCoordinates c (scale • R) x) c = scale * ‖matrixContinuousLinear R x‖ := by
      simp only [affineCoordinates, Matrix.smul_mulVec, dist_eq_norm,
        add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale,
        matrixContinuousLinear_apply]
    _ ≤ scale * (‖matrixContinuousLinear R‖ * 4) := mul_le_mul_of_nonneg_left hmap hscale
    _ = _ := by ring

theorem exists_finite_affine_square_scale {ι : Type*} [Fintype ι]
    (c : ι → Coord) (hc : Function.Injective c) {U : Set Coord}
    (hU : IsOpen U) (hcU : ∀ i, c i ∈ U)
    (R : Matrix (Fin 2) (Fin 2) ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ scale > 0, scale ≤ η ∧
      (∀ i, closedAffineSquare (c i) scale R ⊆ U) ∧
      Pairwise (fun i j => Disjoint (closedAffineSquare (c i) scale R)
        (closedAffineSquare (c j) scale R)) ∧
      ∀ i p, p ∈ closedAffineSquare (c i) scale R → dist p (c i) ≤ η := by
  classical
  have hballs : ∀ i, ∃ a > 0, Metric.ball (c i) a ⊆ U :=
    fun i => Metric.mem_nhds_iff.mp (hU.mem_nhds (hcU i))
  choose a ha haU using hballs
  obtain ⟨ρ, hρ, hρa⟩ := finite_positive_lower_bound Finset.univ a (by simpa using ha)
  let separation : ι × ι → ℝ := fun ij => if ij.1 = ij.2 then 1 else dist (c ij.1) (c ij.2)
  have hsep : ∀ ij ∈ (Finset.univ : Finset (ι × ι)), 0 < separation ij := by
    intro ij _
    dsimp only [separation]
    split_ifs with hij
    · norm_num
    · exact dist_pos.mpr (fun h => hij (hc h))
  obtain ⟨δ, hδ, hδsep⟩ := finite_positive_lower_bound Finset.univ separation hsep
  let t : ℝ := min ρ (min δ η) / 4
  have ht : 0 < t := by dsimp only [t] <;> positivity
  have htρ : t ≤ ρ / 4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have htδ : t ≤ δ / 4 := div_le_div_of_nonneg_right
    ((min_le_right ρ (min δ η)).trans (min_le_left δ η)) (by norm_num)
  have htη : t ≤ η / 4 := div_le_div_of_nonneg_right
    ((min_le_right ρ (min δ η)).trans (min_le_right δ η)) (by norm_num)
  let scale : ℝ := t / (1 + 4 * ‖matrixContinuousLinear R‖)
  have hden : 0 < 1 + 4 * ‖matrixContinuousLinear R‖ := by positivity
  have hscale : 0 < scale := div_pos ht hden
  have hscaleeq : scale * (1 + 4 * ‖matrixContinuousLinear R‖) = t :=
    div_mul_cancel₀ t hden.ne'
  have hscalet : scale ≤ t := by
    nlinarith [mul_nonneg hscale.le (norm_nonneg (matrixContinuousLinear R))]
  have hsize : scale * (4 * ‖matrixContinuousLinear R‖) ≤ t := by nlinarith
  have hcontain (i : ι) : closedAffineSquare (c i) scale R ⊆ Metric.closedBall (c i) t := by
    intro p hp
    exact (closedAffineSquare_dist_le (c i) hscale.le R hp).trans hsize
  refine ⟨scale, hscale, by linarith, ?_, ?_, ?_⟩
  · intro i
    apply Set.Subset.trans (hcontain i)
    apply Set.Subset.trans (Metric.closedBall_subset_ball (show t < a i from by
      have := hρa i (Finset.mem_univ i)
      linarith))
    exact haU i
  · intro i j hij
    have hd : δ < dist (c i) (c j) := by
      simpa only [separation, ite_eq_right hij] using hδsep (i, j) (Finset.mem_univ (i, j))
    exact (Metric.closedBall_disjoint_closedBall (show t + t < dist (c i) (c j) by
      linarith)).mono (hcontain i) (hcontain j)
  · intro i p hp
    have := hcontain i hp
    change dist p (c i) ≤ t at this
    linarith

theorem exists_finset_affine_square_scale (s : Finset Coord) {U : Set Coord}
    (hU : IsOpen U) (hsU : ∀ c ∈ s, c ∈ U)
    (R : Matrix (Fin 2) (Fin 2) ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ scale > 0, scale ≤ η ∧
      (∀ c ∈ s, closedAffineSquare c scale R ⊆ U) ∧
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → Disjoint (closedAffineSquare c scale R)
        (closedAffineSquare d scale R)) ∧
      ∀ c ∈ s, ∀ p ∈ closedAffineSquare c scale R, dist p c ≤ η := by
  classical
  obtain ⟨scale, hscale, hscaleη, hsub, hdisj, hbound⟩ :=
    exists_finite_affine_square_scale (fun c : {c // c ∈ s} => c.val)
      Subtype.val_injective hU (fun c => hsU c.val c.property) R hη
  exact ⟨scale, hscale, hscaleη, fun c hc => hsub ⟨c, hc⟩,
    fun c hc d hd hcd => hdisj (i := ⟨c, hc⟩) (j := ⟨d, hd⟩)
      (fun h => hcd (congrArg Subtype.val h)),
    fun c hc p hp => hbound ⟨c, hc⟩ p hp⟩

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_OrientedPatchSquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

theorem exists_orientedPatchScale (n k : ℕ) (R : OrientationLabel) :
    ∃ scale > 0, scale ≤ accumulatingScale k ∧
      (∀ c ∈ orientedExteriorCenters n k R, closedAffineSquare c scale R.val ⊆
        exteriorOpenLayer n (orientedLayerIndex k R)) ∧
      (∀ c ∈ orientedExteriorCenters n k R, ∀ d ∈ orientedExteriorCenters n k R,
        c ≠ d → Disjoint (closedAffineSquare c scale R.val) (closedAffineSquare d scale R.val)) ∧
      ∀ c ∈ orientedExteriorCenters n k R, ∀ p ∈ closedAffineSquare c scale R.val,
        dist p c ≤ accumulatingScale k :=
  exists_finset_affine_square_scale (orientedExteriorCenters n k R)
    (exteriorOpenLayer_isOpen n (orientedLayerIndex k R))
    (fun _ hc => orientedExteriorCenters_mem_layer n k R hc) R.val (accumulatingScale_pos k)

def orientedPatchScale (n k : ℕ) (R : OrientationLabel) : ℝ :=
  Classical.choose (exists_orientedPatchScale n k R)

def orientedClosedPatch (n k : ℕ) (R : OrientationLabel) (c : Coord) : Set Coord :=
  closedAffineSquare c (orientedPatchScale n k R) R.val

theorem orientedPatchScale_pos (n k : ℕ) (R : OrientationLabel) :
    0 < orientedPatchScale n k R :=
  (Classical.choose_spec (exists_orientedPatchScale n k R)).1

theorem orientedClosedPatch_subset_layer (n k : ℕ) (R : OrientationLabel)
    {c : Coord} (hc : c ∈ orientedExteriorCenters n k R) :
    orientedClosedPatch n k R c ⊆ exteriorOpenLayer n (orientedLayerIndex k R) :=
  (Classical.choose_spec (exists_orientedPatchScale n k R)).2.2.1 c hc

theorem orientedClosedPatches_disjoint_same_layer (n k : ℕ) (R : OrientationLabel)
    {c d : Coord} (hc : c ∈ orientedExteriorCenters n k R)
    (hd : d ∈ orientedExteriorCenters n k R) (hcd : c ≠ d) :
    Disjoint (orientedClosedPatch n k R c) (orientedClosedPatch n k R d) :=
  (Classical.choose_spec (exists_orientedPatchScale n k R)).2.2.2.1 c hc d hd hcd

theorem orientedClosedPatch_subset_closedLayer (n k : ℕ) (R : OrientationLabel)
    {c : Coord} (hc : c ∈ orientedExteriorCenters n k R) :
    orientedClosedPatch n k R c ⊆ exteriorClosedLayer n (orientedLayerIndex k R) :=
  (orientedClosedPatch_subset_layer n k R hc).trans
    (exteriorOpenLayer_subset_closed n (orientedLayerIndex k R))

theorem orientedClosedPatches_disjoint_different_layers (n : ℕ)
    {a b : ℕ × OrientationLabel} (hab : a ≠ b) {c d : Coord}
    (hc : c ∈ orientedExteriorCenters n a.1 a.2)
    (hd : d ∈ orientedExteriorCenters n b.1 b.2) :
    Disjoint (orientedClosedPatch n a.1 a.2 c) (orientedClosedPatch n b.1 b.2 d) :=
  (orientedExteriorLayers_disjoint n hab).mono
    (orientedClosedPatch_subset_closedLayer n a.1 a.2 hc)
    (orientedClosedPatch_subset_closedLayer n b.1 b.2 hd)

theorem orientedClosedPatches_disjoint_different_disks {n m : ℕ} (hnm : n ≠ m)
    (k l : ℕ) (R S : OrientationLabel) {c d : Coord}
    (hc : c ∈ orientedExteriorCenters n k R)
    (hd : d ∈ orientedExteriorCenters m l S) :
    Disjoint (orientedClosedPatch n k R c) (orientedClosedPatch m l S d) :=
  (exteriorClosedLayers_disjoint_different_disks hnm (orientedLayerIndex k R)
    (orientedLayerIndex l S)).mono (orientedClosedPatch_subset_closedLayer n k R hc)
      (orientedClosedPatch_subset_closedLayer m l S hd)

theorem orientedClosedPatch_disjoint_every_disk (n k : ℕ) (R : OrientationLabel)
    {c : Coord} (hc : c ∈ orientedExteriorCenters n k R) (m : ℕ) :
    Disjoint (orientedClosedPatch n k R c) (accumulatingDisk m) :=
  (exteriorClosedLayer_disjoint_every_disk n (orientedLayerIndex k R) m).mono_left
    (orientedClosedPatch_subset_closedLayer n k R hc)

theorem orientedClosedPatch_subset_enlarged (n k : ℕ) (R : OrientationLabel)
    {c : Coord} (hc : c ∈ orientedExteriorCenters n k R) :
    orientedClosedPatch n k R c ⊆ enlargedAccumulatingDisk n :=
  (orientedClosedPatch_subset_closedLayer n k R hc).trans
    (exteriorClosedLayer_subset_enlarged n (orientedLayerIndex k R))

theorem orientedPatchMatrix_isUnit (n k : ℕ) (R : OrientationLabel) :
    IsUnit (orientedPatchScale n k R • R.val) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_smul, (orientationRotations_properties R.property).2.2]
  exact mul_ne_zero (pow_ne_zero _ (orientedPatchScale_pos n k R).ne') one_ne_zero

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_PatchCurvatureProfiles
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

def openPatchBox : Set Coord := {x | ∀ i, x i ∈ Set.Ioo (-4 : ℝ) 4}

theorem mem_openPatchBox_iff_norm_lt (x : Coord) :
    x ∈ openPatchBox ↔ ‖x‖ < 4 := by
  rw [pi_norm_lt_iff (by norm_num : (0 : ℝ) < 4)]
  simp only [openPatchBox, Set.mem_ofPred_eq, Set.mem_Ioo, Real.norm_eq_abs, abs_lt]

def patchBoxCutoff (p : Coord) : ℝ := patchAxisCutoff (p 0) * patchAxisCutoff (p 1)

theorem patchBoxCutoff_contDiff : ContDiff ℝ ∞ patchBoxCutoff :=
  (patchAxisCutoff_contDiff.comp (contDiff_apply ℝ ℝ 0)).mul
    (patchAxisCutoff_contDiff.comp (contDiff_apply ℝ ℝ 1))

theorem patchBoxCutoff_support_bound {p : Coord} (hp : patchBoxCutoff p ≠ 0) :
    ‖p‖ < 15 / 4 := by
  have hprod := mul_ne_zero_iff.mp hp
  apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 15 / 4)).mpr
  intro i
  fin_cases i
  · change |p 0| < 15 / 4
    exact patchAxisCutoff_support_bound hprod.1
  · change |p 1| < 15 / 4
    exact patchAxisCutoff_support_bound hprod.2

def localPatchProfile (p : Coord) : ℝ := patchBoxCutoff p * modelCurvature 1 p

theorem localPatchProfile_contDiff : ContDiff ℝ ∞ localPatchProfile :=
  patchBoxCutoff_contDiff.mul (modelCurvature_contDiff 1)

theorem localPatchProfile_tsupport_bound :
    tsupport localPatchProfile ⊆ Metric.closedBall (0 : Coord) (15 / 4) := by
  apply closure_minimal _ isClosed_closedBall
  intro p hp
  have hcut : patchBoxCutoff p ≠ 0 := (mul_ne_zero_iff.mp hp).1
  change dist p 0 ≤ 15 / 4
  simpa only [dist_zero_right] using (patchBoxCutoff_support_bound hcut).le

theorem localPatchProfile_hasCompactSupport : HasCompactSupport localPatchProfile :=
  (isCompact_closedBall (0 : Coord) (15 / 4)).of_isClosed_subset
    (isClosed_tsupport _) localPatchProfile_tsupport_bound

theorem localPatchProfile_tsupport_strictly_inside : tsupport localPatchProfile ⊆ openPatchBox := by
  intro p hp
  apply (mem_openPatchBox_iff_norm_lt p).mpr
  have hnorm : ‖p‖ ≤ 15 / 4 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using localPatchProfile_tsupport_bound hp
  linarith

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_AssemblyProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter

namespace SmoothLocal.Geometry

abbrev PatchAddress := Σ n : ℕ, Σ k : ℕ, Σ R : OrientationLabel,
  {c : Coord // c ∈ orientedExteriorCenters n k R}

instance instCountablePatchAddress : Countable PatchAddress := by
  classical
  let : ∀ (n k : ℕ) (R : OrientationLabel),
      Finite {c : Coord // c ∈ orientedExteriorCenters n k R} :=
    fun n k R => (orientedExteriorCenters n k R).finite_toSet.to_subtype
  infer_instance

abbrev AssemblyProfileIndex := ℕ ⊕ PatchAddress

instance assemblyProfileEncodable : Encodable AssemblyProfileIndex :=
  Encodable.ofCountable AssemblyProfileIndex

def patchAddressCarrier (a : PatchAddress) : Set Coord :=
  orientedClosedPatch a.1 a.2.1 a.2.2.1 a.2.2.2.val

def assemblyCarrier : AssemblyProfileIndex → Set Coord
  | .inl n => accumulatingDisk n
  | .inr a => patchAddressCarrier a

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_QuotientLowRecurrence
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
namespace LowQuotient

variable {U : Set Coord} {a b : Coord → ℝ} {p : Coord}

theorem iterated_contDiffOn (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U)
    (ds : List (Fin 2)) : ContDiffOn ℝ ∞ (iteratedCoordPartial ds a) U := by
  induction ds with
  | nil => exact ha
  | cons i ds ih => exact partial_contDiffOn ih hU i

theorem iterated_differentiableAt (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U)
    (hp : p ∈ U) (ds : List (Fin 2)) :
    DifferentiableAt ℝ (iteratedCoordPartial ds a) p :=
  ((iterated_contDiffOn ha hU ds).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

end LowQuotient
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

variable {U : Set Coord} {a b : Coord → ℝ} {M c : ℝ}

theorem quotient_bound_zero (hM : 0 ≤ M) (hc : 0 < c)
    (ha0 : ∀ p ∈ U, |a p| ≤ M) (hden : ∀ p ∈ U, c ≤ |b p|)
    {p : Coord} (hp : p ∈ U) : |a p / b p| ≤ bound0 M c :=
  abs_div_bound hM (ha0 p hp) hc (hden p hp)

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

theorem mono {f : Coord → ℝ} {U : Set Coord} {n m : ℕ} {M N : ℝ}
    (hf : CoordinateBound f U n M) (hm : m ≤ n) (hMN : M ≤ N) :
    CoordinateBound f U m N := fun ds hds p hp => (hf ds (hds.trans hm) p hp).trans hMN

theorem iterated_append (ds es : List (Fin 2)) (f : Coord → ℝ) :
    iteratedCoordPartial (ds ++ es) f = iteratedCoordPartial ds (iteratedCoordPartial es f) := by
  induction ds with
  | nil => rfl
  | cons i ds ih => simp only [List.cons_append, iteratedCoordPartial, ih]

theorem partial_bound {f : Coord → ℝ} {U : Set Coord} {n : ℕ} {M : ℝ}
    (hf : CoordinateBound f U (n + 1) M) (i : Fin 2) :
    CoordinateBound (coordPartial i f) U n M := by
  intro ds hds p hp
  have hh := hf (ds ++ [i]) (by simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right hds 1) p hp
  rw [iterated_append] at hh
  exact hh

end CoordinateBound
end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

namespace CompatibilityCalculus

theorem coordPartial_quadratic
    {A B C X Y : Coord → ℝ} {p : Coord}
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p)
    (hC : DifferentiableAt ℝ C p) (hX : DifferentiableAt ℝ X p)
    (hY : DifferentiableAt ℝ Y p) (k : Fin 2) :
    coordPartial k (fun q => A q * (X q) ^ 2 -
      2 * B q * X q * Y q + C q * (Y q) ^ 2) p =
      coordPartial k A p * (X p) ^ 2 + 2 * A p * X p * coordPartial k X p -
        (2 * coordPartial k B p * X p * Y p +
          2 * B p * coordPartial k X p * Y p +
          2 * B p * X p * coordPartial k Y p) +
        coordPartial k C p * (Y p) ^ 2 + 2 * C p * Y p * coordPartial k Y p := by
  have hd := ((hA.hasFDerivAt.fun_mul (hX.hasFDerivAt.fun_mul hX.hasFDerivAt)).sub
    (((hB.hasFDerivAt.const_mul (2 : ℝ)).fun_mul hX.hasFDerivAt).fun_mul hY.hasFDerivAt)).add
      (hC.hasFDerivAt.fun_mul (hY.hasFDerivAt.fun_mul hY.hasFDerivAt))
  simp only [Pi.add_def, Pi.sub_def] at hd
  simp only [pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

end CompatibilityCalculus

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_MetricTwoJet
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace MetricJetCalculus

theorem coordPartial_const_mul_at {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (c : ℝ) (i : Fin 2) :
    coordPartial i (fun q => c * f q) p = c * coordPartial i f p := by
  simp [coordPartial, fderiv_const_mul hf]

end MetricJetCalculus

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

def tensorPatchSum (η : ℕ → MetricField) : MetricField := flatPatchSum η

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_IntrinsicCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord} {p : Coord}

def curvatureFactor (g : MetricField) (l k i j : Fin 2) (p : Coord) : ℝ :=
  (if l = i then g p j k else 0) - (if l = j then g p i k else 0)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_SmoothCurry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology Interval ContDiff

namespace SmoothLocal.ODE

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem continuousMap_smooth_of_eval_derivative_sequence
    {a b : ℝ} (F : ℕ → ℝ → C(X, E))
    (hcont : ∀ n, ContinuousOn (F n) (Ioo a b))
    (hpoint : ∀ n t, t ∈ Ioo a b → ∀ x : X,
      HasDerivAt (fun s => F n s x) (F (n + 1) t x) t) :
    ∀ n, ContDiffOn ℝ ∞ (F n) (Ioo a b) := by
  have hd (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (F n) (F (n + 1) t) t :=
    hasDerivAt_continuousMap_of_eval (hcont (n + 1)) (hpoint n) ht
  have hnat : ∀ m : ℕ, ∀ n : ℕ, ContDiffOn ℝ m (F n) (Ioo a b) := by
    intro m
    induction m with
    | zero =>
        intro n
        simpa only [Nat.cast_zero, contDiffOn_zero] using hcont n
    | succ m hm =>
        intro n
        have hnext : ContDiffOn ℝ ((m : ℕ∞ω) + 1) (F n) (Ioo a b) := by
          rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
          refine ⟨fun t ht => (hd n t ht).differentiableAt.differentiableWithinAt,
            by simp, ?_⟩
          exact (hm (n + 1)).congr (fun t ht => (hd n t ht).deriv)
        simpa only [Nat.cast_add, Nat.cast_one] using hnext
  intro n
  exact contDiffOn_infty.mpr (fun m => hnat m n)

theorem smooth_curry_of_joint_derivative_sequence
    {a b : ℝ} (H : ℕ → ℝ → X → E)
    (hjoint : ∀ n, ContinuousOn (Function.uncurry (H n))
      ((Ioo a b) ×ˢ (Set.univ : Set X)))
    (hpoint : ∀ n t, t ∈ Ioo a b → ∀ x : X,
      HasDerivAt (fun s => H n s x) (H (n + 1) t x) t) :
    ∀ n, ContDiffOn ℝ ∞ (fun t => ContinuousMap.mkD (H n t) 0) (Ioo a b) := by
  let F : ℕ → ℝ → C(X, E) := fun n t => ContinuousMap.mkD (H n t) 0
  have hslice (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) : Continuous (H n t) :=
    (hjoint n).comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨ht, Set.mem_univ _⟩)
  have heval (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : X) : F n t x = H n t x := by
    dsimp only [F]
    rw [ContinuousMap.mkD_of_continuous (hslice n t ht)]
    rfl
  have hcont (n : ℕ) : ContinuousOn (F n) (Ioo a b) :=
    ContinuousMap.continuousOn_mkD_of_uncurry (H n) 0 (hjoint n)
  have hpointF (n : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : X) :
      HasDerivAt (fun s => F n s x) (F (n + 1) t x) t := by
    have hevent : (fun s => F n s x) =ᶠ[𝓝 t] (fun s => H n s x) :=
      Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2)
        (fun s hs => heval n s hs x)
    rw [heval (n + 1) t ht x]
    exact (hpoint n t ht x).congr_of_eventuallyEq hevent
  exact continuousMap_smooth_of_eval_derivative_sequence F hcont hpointF

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

def curvatureYDerivative (K : Coord → ℝ) : ℕ → Coord → ℝ
  | 0 => K
  | n + 1 => coordPartial 1 (curvatureYDerivative K n)

def coordinateCurvatureFamily (K : Coord → ℝ) (r : ℝ) (y : ℝ) : IntervalFunctions r :=
  ContinuousMap.mkD (fun x : Icc (-r) r => K (coordinatePoint x y)) 0

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

def intervalFamilyJet (r : ℝ) (hr : 0 < r)
    (F : ℝ → IntervalFunctions r) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  intervalExtension r hr (iteratedDeriv n F p.2) p.1

theorem intervalFamilyJet_continuousOn (r : ℝ) (hr : 0 < r)
    {s : Set ℝ} (hs : IsOpen s) {F : ℝ → IntervalFunctions r}
    (hF : ContDiffOn ℝ ∞ F s) (n : ℕ) :
    ContinuousOn (intervalFamilyJet r hr F n) (univ ×ˢ s) :=
  intervalExtension_family_continuousOn r hr
    (iteratedDeriv_contDiffOn_of_isOpen hs hF n).continuousOn

theorem intervalFamilyJet_hasDerivAt_y (r : ℝ) (hr : 0 < r)
    {s : Set ℝ} (hs : IsOpen s) {F : ℝ → IntervalFunctions r}
    (hF : ContDiffOn ℝ ∞ F s) (n : ℕ) (x : ℝ)
    {y : ℝ} (hy : y ∈ s) :
    HasDerivAt (fun t => intervalFamilyJet r hr F n (x, t))
      (intervalFamilyJet r hr F (n + 1) (x, y)) y := by
  have hd : HasDerivAt (iteratedDeriv n F) (iteratedDeriv (n + 1) F y) y := by
    rw [iteratedDeriv_succ]
    exact (((iteratedDeriv_contDiffOn_of_isOpen hs hF n).contDiffAt
      (hs.mem_nhds hy)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt
  exact intervalExtension_family_hasDerivAt r hr hd x

theorem intervalFamilyJet_hasDerivAt_x_of_primitive
    (r : ℝ) (hr : 0 < r) {s : Set ℝ} (hs : IsOpen s)
    {F P : ℝ → IntervalFunctions r} (hP : ContDiffOn ℝ ∞ P s)
    (c : ℝ)
    (hFP : ∀ y ∈ s,
      F y = ContinuousMap.const (Icc (-r) r) c + primitiveCLM r hr (P y))
    (n : ℕ) {x y : ℝ} (hx : x ∈ Ioo (-r) r) (hy : y ∈ s) :
    HasDerivAt (fun t => intervalFamilyJet r hr F n (t, y))
      (intervalFamilyJet r hr P n (x, y)) x := by
  cases n with
  | zero =>
      simp only [intervalFamilyJet, iteratedDeriv_zero]
      rw [hFP y hy]
      exact (intervalExtension_primitive_hasDerivAt r hr (P y) hx).const_add c
  | succ n =>
      have he : iteratedDeriv (n + 1) F y =
          primitiveCLM r hr (iteratedDeriv (n + 1) P y) := by
        have hev : F =ᶠ[𝓝 y] (fun t =>
            ContinuousMap.const (Icc (-r) r) c + primitiveCLM r hr (P t)) := by
          filter_upwards [hs.mem_nhds hy] with t ht
          exact hFP t ht
        rw [hev.iteratedDeriv_eq (n + 1), iteratedDeriv_const_add (Nat.zero_lt_succ n)]
        exact iteratedDeriv_clm_comp (primitiveCLM r hr) (n + 1)
          (hP.contDiffAt (hs.mem_nhds hy))
      simp only [intervalFamilyJet]
      rw [he]
      exact intervalExtension_primitive_hasDerivAt r hr _ hx

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

def patchCompact : Compacts Coord := ⟨patchBox, isCompact_Icc⟩

abbrev SupportedTensor :=
  ContDiffMapSupportedIn Coord (Matrix (Fin 2) (Fin 2) ℝ) ⊤ patchCompact

end SmoothLocal.Perturbation

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

def affineTensorJetFactor (R : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) : ℝ :=
  ‖affineTensorCongruence R‖ * ‖matrixContinuousLinear R⁻¹‖^n

def affineTensorOrderFactor (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ) : ℝ :=
  1 + ‖affineTensorCongruence R‖ * (1 + ‖matrixContinuousLinear R⁻¹‖)^N

theorem affineTensorOrderFactor_pos (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ) :
    0 < affineTensorOrderFactor R N := by
  unfold affineTensorOrderFactor
  positivity

end SmoothLocal.Geometry

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

def patchAddressCenter (a : PatchAddress) : Coord := a.2.2.2.val

def patchAddressMatrix (a : PatchAddress) : Matrix (Fin 2) (Fin 2) ℝ :=
  orientedPatchScale a.1 a.2.1 a.2.2.1 • a.2.2.1.val

def patchTensorAddress (j : ℕ) : Option PatchAddress :=
  match Encodable.decode₂ AssemblyProfileIndex j with
  | some (.inr a) => some a
  | _ => none

end SmoothLocal.Geometry

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

theorem explicitDriftError_pointwise_bound
    (h E T J : Coord → ℝ) (p : Coord) (c BE Bh BT BJ : ℝ)
    (hc : 0 < c) (hh : c ≤ |h p|)
    (hE : |E p| ≤ BE) (hhy : |coordPartial 1 h p| ≤ Bh)
    (hT : |T p| ≤ BT) (hJ : |J p| ≤ BJ) :
    |explicitDriftError h E T J p| ≤
      BE / c ^ 2 * (BT + Bh / c) + BJ / c := by
  exact explicitDriftError_scalar_bound (h p) (E p) (coordPartial 1 h p)
    (T p) (J p) c BE Bh BT BJ hc hh hE hhy hT hJ

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_ActualDriftCoefficients
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Geometry

def darbouxG (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  heightEnergy g z p / (covHessian g z p 1 1) ^ 2

def connectionTraceY (g : MetricField) (p : Coord) : ℝ :=
  christoffel g 0 0 1 p + christoffel g 1 1 1 p

def driftJ (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  (g p 0 0 - hessianQuotient g z p * g p 0 1) * coordPartial 1 z p -
    (g p 0 1 - hessianQuotient g z p * g p 1 1) * coordPartial 0 z p

def curvatureDriftError (g : MetricField) (z : Coord → ℝ) : Coord → ℝ :=
  explicitDriftError (fun p => covHessian g z p 1 1) (heightEnergy g z)
    (connectionTraceY g) (driftJ g z)

theorem curvatureDriftError_eq (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    curvatureDriftError g z p =
      darbouxG g z p *
        (connectionTraceY g p -
          coordPartial 1 (fun q => covHessian g z q 1 1) p / covHessian g z p 1 1) +
        driftJ g z p / covHessian g z p 1 1 := rfl

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

theorem darbouxG_pos (g : MetricField) (z : Coord → ℝ) (p : Coord)
    (hE : 0 < heightEnergy g z p) (hyy : covHessian g z p 1 1 ≠ 0) :
    0 < darbouxG g z p :=
  height_energy_quotient_pos (heightEnergy g z p) (covHessian g z p 1 1) hE hyy

theorem curvatureDriftError_bound
    (g : MetricField) (z : Coord → ℝ) (p : Coord) (c BE Bh BT BJ : ℝ)
    (hc : 0 < c) (hh : c ≤ |covHessian g z p 1 1|)
    (hE : |heightEnergy g z p| ≤ BE)
    (hhy : |coordPartial 1 (fun q => covHessian g z q 1 1) p| ≤ Bh)
    (hT : |connectionTraceY g p| ≤ BT) (hJ : |driftJ g z p| ≤ BJ) :
    |curvatureDriftError g z p| ≤ BE / c ^ 2 * (BT + Bh / c) + BJ / c :=
  explicitDriftError_pointwise_bound (fun q => covHessian g z q 1 1)
    (heightEnergy g z) (connectionTraceY g) (driftJ g z) p c BE Bh BT BJ
      hc hh hE hhy hT hJ

theorem driftJ_bound
    (g : MetricField) (z : Coord → ℝ) (p : Coord) (M : ℝ)
    (hMetric : ∀ i j : Fin 2, |g p i j| ≤ M)
    (hHeight : ∀ i : Fin 2, |coordPartial i z p| ≤ M)
    (hq : |hessianQuotient g z p| ≤ (1 / 100 : ℝ)) :
    |driftJ g z p| ≤ (202 / 100 : ℝ) * M ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg (g p 0 0)).trans (hMetric 0 0)
  have heps : (0 : ℝ) ≤ 1 / 100 := by norm_num
  have htriangle (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le a 0 b
  have hqg (i j : Fin 2) :
      |hessianQuotient g z p * g p i j| ≤ (1 / 100 : ℝ) * M := by
    rw [abs_mul]
    exact mul_le_mul hq (hMetric i j) (abs_nonneg _) heps
  have hfactor (a b c d : Fin 2) :
      |g p a b - hessianQuotient g z p * g p c d| ≤ M + (1 / 100 : ℝ) * M :=
    (htriangle _ _).trans (add_le_add (hMetric a b) (hqg c d))
  have hfactor_nonneg : 0 ≤ M + (1 / 100 : ℝ) * M :=
    add_nonneg hM (mul_nonneg heps hM)
  calc
    |driftJ g z p| ≤
        |(g p 0 0 - hessianQuotient g z p * g p 0 1) * coordPartial 1 z p| +
          |(g p 0 1 - hessianQuotient g z p * g p 1 1) * coordPartial 0 z p| :=
      htriangle _ _
    _ = |g p 0 0 - hessianQuotient g z p * g p 0 1| * |coordPartial 1 z p| +
          |g p 0 1 - hessianQuotient g z p * g p 1 1| * |coordPartial 0 z p| := by
      rw [abs_mul, abs_mul]
    _ ≤ (M + (1 / 100 : ℝ) * M) * M + (M + (1 / 100 : ℝ) * M) * M :=
      add_le_add
        (mul_le_mul (hfactor 0 0 0 1) (hHeight 1) (abs_nonneg _) hfactor_nonneg)
        (mul_le_mul (hfactor 0 1 1 1) (hHeight 0) (abs_nonneg _) hfactor_nonneg)
    _ = (202 / 100 : ℝ) * M ^ 2 := by ring

theorem curvatureDriftError_bound_from_low_data
    (g : MetricField) (z : Coord → ℝ) (p : Coord) (c BE Bh BT M : ℝ)
    (hc : 0 < c) (hh : c ≤ |covHessian g z p 1 1|)
    (hE : |heightEnergy g z p| ≤ BE)
    (hhy : |coordPartial 1 (fun q => covHessian g z q 1 1) p| ≤ Bh)
    (hT : |connectionTraceY g p| ≤ BT)
    (hMetric : ∀ i j : Fin 2, |g p i j| ≤ M)
    (hHeight : ∀ i : Fin 2, |coordPartial i z p| ≤ M)
    (hq : |hessianQuotient g z p| ≤ (1 / 100 : ℝ)) :
    |curvatureDriftError g z p| ≤
      BE / c ^ 2 * (BT + Bh / c) + ((202 / 100 : ℝ) * M ^ 2) / c :=
  curvatureDriftError_bound g z p c BE Bh BT ((202 / 100 : ℝ) * M ^ 2)
    hc hh hE hhy hT (driftJ_bound g z p M hMetric hHeight hq)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_MetricInverseJetBounds
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord} {G d : ℝ}

theorem inverseMetric_eq_adjugate_div (g : MetricField) (i j : Fin 2) :
    (fun p => inverseMetric g p i j) = (fun p => (g p).adjugate i j / (g p).det) := by
  funext p
  simp [inverseMetric, Matrix.inv_def, Ring.inverse_eq_inv, div_eq_mul_inv, smul_eq_mul, mul_comm]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_HessianJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.Geometry

def connectionBracket (g : MetricField) (i j l : Fin 2) (p : Coord) : ℝ :=
  coordPartial i (fun x => g x j l) p + coordPartial j (fun x => g x i l) p -
    coordPartial l (fun x => g x i j) p

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_DarbouxJet
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def christoffelAlongD (g : MetricField) (p : Coord) (q : ℝ) (i : Fin 2) : ℝ :=
  ∑ a, ∑ b, christoffel g i a b p * jetDriftVector q a * jetDriftVector q b

namespace DarbouxJetCalculus

theorem coordPartial_const (c : ℝ) (i : Fin 2) (u : Coord) :
    coordPartial i (fun _ : Coord => c) u = 0 := by
  simp [coordPartial]

theorem coordPartial_eval (i j : Fin 2) (u : Coord) :
    coordPartial i (fun v : Coord => v j) u = if j = i then 1 else 0 := by
  simp [coordPartial, (hasFDerivAt_apply j u).fderiv, Pi.single_apply]

end DarbouxJetCalculus

theorem jetConnection_differentiableAt (g : MetricField) (p u : Coord) (a b : Fin 2) :
    DifferentiableAt ℝ (jetConnection g p a b) u := by
  have h0 : DifferentiableAt ℝ (fun v : Coord => christoffel g 0 a b p * v 0) u :=
    (differentiableAt_apply (𝕜 := ℝ) 0 u).const_mul (christoffel g 0 a b p)
  have h1 : DifferentiableAt ℝ (fun v : Coord => christoffel g 1 a b p * v 1) u :=
    (differentiableAt_apply (𝕜 := ℝ) 1 u).const_mul (christoffel g 1 a b p)
  change DifferentiableAt ℝ (fun v => ∑ r, christoffel g r a b p * v r) u
  simpa only [Fin.sum_univ_two, Pi.add_def] using h0.add h1

theorem jetMixed_differentiableAt (g : MetricField) (p u : Coord) (b : ℝ) :
    DifferentiableAt ℝ (jetMixed g p b) u := by
  change DifferentiableAt ℝ (fun v => b - jetConnection g p 0 1 v) u
  simpa only [Pi.sub_def] using
    (differentiableAt_const (𝕜 := ℝ) b).sub (jetConnection_differentiableAt g p u 0 1)

theorem jetYY_differentiableAt (g : MetricField) (p u : Coord) (c : ℝ) :
    DifferentiableAt ℝ (jetYY g p c) u := by
  change DifferentiableAt ℝ (fun v => c - jetConnection g p 1 1 v) u
  simpa only [Pi.sub_def] using
    (differentiableAt_const (𝕜 := ℝ) c).sub (jetConnection_differentiableAt g p u 1 1)

theorem jetEnergy_differentiableAt (g : MetricField) (p u : Coord) :
    DifferentiableAt ℝ (jetEnergy g p) u := by
  have h0 := differentiableAt_apply (𝕜 := ℝ) 0 u
  have h1 := differentiableAt_apply (𝕜 := ℝ) 1 u
  change DifferentiableAt ℝ (fun v : Coord => (g p).det -
    (g p 1 1 * (v 0) ^ 2 - (g p 0 1 + g p 1 0) * v 0 * v 1 +
      g p 0 0 * (v 1) ^ 2)) u
  simpa only [Pi.pow_apply, Pi.add_def, Pi.sub_def, Pi.mul_apply] using
    (differentiableAt_const (𝕜 := ℝ) (g p).det).sub
    ((((h0.pow 2).const_mul (g p 1 1)).sub
      ((h0.const_mul (g p 0 1 + g p 1 0)).mul h1)).add
        ((h1.pow 2).const_mul (g p 0 0)))

theorem coordPartial_jetEnergy (g : MetricField) (p u : Coord) (i : Fin 2) :
    coordPartial i (jetEnergy g p) u =
      if i = 0 then -2 * g p 1 1 * u 0 + (g p 0 1 + g p 1 0) * u 1
      else (g p 0 1 + g p 1 0) * u 0 - 2 * g p 0 0 * u 1 := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) 0 u
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) 1 u
  have hQ := (((h0.fun_mul h0).const_mul (g p 1 1)).sub
    ((h0.const_mul (g p 0 1 + g p 1 0)).fun_mul h1)).add
      ((h1.fun_mul h1).const_mul (g p 0 0))
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (g p).det u).sub hQ
  simp only [Pi.add_def, Pi.sub_def] at hd
  change fderiv ℝ (fun v : Coord => (g p).det -
    (g p 1 1 * (v 0) ^ 2 - (g p 0 1 + g p 1 0) * v 0 * v 1 +
      g p 0 0 * (v 1) ^ 2)) u (Pi.single i 1) = _
  simp only [pow_two]
  rw [hd.fderiv]
  fin_cases i <;> simp <;> ring

theorem jetNumerator_differentiableAt (g : MetricField) (p u : Coord) (b : ℝ) :
    DifferentiableAt ℝ (jetNumerator g p b) u := by
  have hsq : DifferentiableAt ℝ (fun v => (jetMixed g p b v) ^ 2) u := by
    simpa only [pow_two] using
      ((jetMixed_differentiableAt g p u b).hasFDerivAt.fun_mul
        (jetMixed_differentiableAt g p u b).hasFDerivAt).differentiableAt
  have hKE : DifferentiableAt ℝ
      (fun v => gaussianCurvature g p * jetEnergy g p v) u :=
    (jetEnergy_differentiableAt g p u).const_mul (gaussianCurvature g p)
  change DifferentiableAt ℝ (fun v => (jetMixed g p b v) ^ 2 +
    gaussianCurvature g p * jetEnergy g p v) u
  simpa only [Pi.add_def] using hsq.add hKE

theorem solvedDarboux_deriv_b (g : MetricField) (p u : Coord) (b c : ℝ)
    (_hne : jetYY g p c u ≠ 0) :
    deriv (fun t => solvedDarboux g p t c u) b =
      2 * (jetMixed g p b u / jetYY g p c u) := by
  have hd := (((((hasDerivAt_id b).sub_const (jetConnection g p 0 1 u)).pow 2).add_const
    (gaussianCurvature g p * jetEnergy g p u)).div_const (jetYY g p c u)).const_add
      (jetConnection g p 0 0 u)
  simp only [Pi.pow_apply, id_eq] at hd
  change deriv (fun t => jetConnection g p 0 0 u +
    ((t - jetConnection g p 0 1 u) ^ 2 + gaussianCurvature g p * jetEnergy g p u) /
      jetYY g p c u) b = _
  rw [hd.deriv]
  simp only [jetMixed, mul_one]
  ring

theorem solvedDarboux_deriv_c (g : MetricField) (p u : Coord) (b c : ℝ)
    (hne : jetYY g p c u ≠ 0) :
    deriv (fun t => solvedDarboux g p b t u) c =
      -((jetMixed g p b u / jetYY g p c u) ^ 2 +
        gaussianCurvature g p * jetEnergy g p u / (jetYY g p c u) ^ 2) := by
  have hdH := (hasDerivAt_id c).sub_const (jetConnection g p 1 1 u)
  have hd := ((hasDerivAt_const c (jetNumerator g p b u)).div hdH hne).const_add
    (jetConnection g p 0 0 u)
  simp only [Pi.div_apply, id_eq] at hd
  change deriv (fun t => jetConnection g p 0 0 u +
    jetNumerator g p b u / (t - jetConnection g p 1 1 u)) c = _
  rw [hd.deriv]
  change (0 * jetYY g p c u - jetNumerator g p b u * 1) / (jetYY g p c u) ^ 2 = _
  simp only [jetNumerator]
  field_simp [hne]
  ring

theorem jetMixed_at_height (g : MetricField) (p : Coord) (z : Coord → ℝ) :
    jetMixed g p (coordPartial 0 (coordPartial 1 z) p) (fun i => coordPartial i z p) =
      covHessian g z p 0 1 := rfl

theorem jetYY_at_height (g : MetricField) (p : Coord) (z : Coord → ℝ) :
    jetYY g p (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p) =
      covHessian g z p 1 1 := rfl

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_WeightPrimitive
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem point_mem_rectangle {R a b x y : ℝ}
    (hx : x ∈ Ioo (-R) R) (hy : y ∈ Ioo a b) :
    coordinatePoint x y ∈ coordinateRectangle R a b := by
  simpa [coordinateRectangle, coordinatePoint] using And.intro hx hy

theorem point_eta (p : Coord) : coordinatePoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> simp [coordinatePoint]

theorem point_hasDerivAt_t (x y : ℝ) :
    HasDerivAt (fun t => coordinatePoint t y) (Pi.single 0 (1 : ℝ) : Coord) x := by
  simpa [coordinatePoint] using
    ((hasDerivAt_id x).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add_const
      (y • (Pi.single 1 (1 : ℝ) : Coord))

def coordinatePrimitive (B : Coord → ℝ) (p : Coord) : ℝ :=
  ∫ t in 0..p 0, B (coordinatePoint t (p 1))

variable {B : Coord → ℝ} {R a b : ℝ}

theorem coefficientFamily_apply_on_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hrR : r < R) {y : ℝ} (hy : y ∈ Ioo a b) (x : Icc (-r) r) :
    coordinateCurvatureFamily B r y x = B (coordinatePoint x y) := by
  have hc : Continuous (fun t : Icc (-r) r => B (coordinatePoint t y)) :=
    hB.continuousOn.comp_continuous (by unfold coordinatePoint; fun_prop)
      (fun t => point_mem_rectangle (compact_t_mem_rectangle_interval hrR t) hy)
  unfold coordinateCurvatureFamily
  rw [ContinuousMap.mkD_of_continuous hc]
  rfl

theorem primitiveFamily_joint_smooth
    (r : ℝ) (hr : 0 < r) {F : ℝ → IntervalFunctions r}
    (hF : ContDiffOn ℝ ∞ F (Ioo a b))
    (hFjets : ∀ j, ContDiffOn ℝ ∞ (intervalFamilyJet r hr F j)
      (Ioo (-r) r ×ˢ Ioo a b)) :
    ∀ j, ContDiffOn ℝ ∞
      (intervalFamilyJet r hr (fun y => primitiveCLM r hr (F y)) j)
      (Ioo (-r) r ×ˢ Ioo a b) := by
  let P : ℝ → IntervalFunctions r := fun y => primitiveCLM r hr (F y)
  let D : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo a b
  have hD : IsOpen D := isOpen_Ioo.prod isOpen_Ioo
  have hP : ContDiffOn ℝ ∞ P (Ioo a b) := contDiffOn_const.clm_apply hF
  have hdx (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun x => intervalFamilyJet r hr P j (x, p.2))
        (intervalFamilyJet r hr F j p) p.1 := by
    apply intervalFamilyJet_hasDerivAt_x_of_primitive r hr isOpen_Ioo hF 0 _ j hp.1 hp.2
    intro y hy
    change primitiveCLM r hr (F y) = 0 + primitiveCLM r hr (F y)
    rw [zero_add]
  have hdy (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun y => intervalFamilyJet r hr P j (p.1, y))
        (intervalFamilyJet r hr P (j + 1) p) p.2 :=
    intervalFamilyJet_hasDerivAt_y r hr isOpen_Ioo hP j p.1 hp.2
  have hnat : ∀ n : ℕ, ∀ j,
      ContDiffOn ℝ n (intervalFamilyJet r hr P j) D := by
    intro n
    induction n with
    | zero =>
        intro j
        simpa only [Nat.cast_zero, contDiffOn_zero] using
          (intervalFamilyJet_continuousOn r hr isOpen_Ioo hP j).mono
            (fun p hp => ⟨mem_univ p.1, hp.2⟩)
    | succ n hn =>
        intro j
        exact contDiffOn_succ_of_continuous_partials hD n
          (contDiffOn_infty.mp (hFjets j) n) (hn (j + 1)) (hdx j) (hdy j)
  intro j
  exact contDiffOn_infty.mpr (fun n => hnat n j)

def clampedPrimitive (B : Coord → ℝ) (r : ℝ) (hr : 0 < r) (p : ℝ × ℝ) : ℝ :=
  intervalExtension r hr (primitiveCLM r hr (coordinateCurvatureFamily B r p.2)) p.1

theorem clampedPrimitive_eq_integral
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hr : 0 < r) (hrR : r < R)
    {x y : ℝ} (hx : x ∈ Ioo (-r) r) (hy : y ∈ Ioo a b) :
    clampedPrimitive B r hr (x, y) = ∫ t in 0..x, B (coordinatePoint t y) := by
  unfold clampedPrimitive
  rw [intervalExtension_apply_of_mem r hr _ ⟨hx.1.le, hx.2.le⟩, primitiveCLM_apply]
  apply intervalIntegral.integral_congr
  intro t ht
  have hz : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr.le⟩
  have htmem : t ∈ Icc (-r) r := uIcc_subset_Icc hz ⟨hx.1.le, hx.2.le⟩ ht
  rw [intervalExtension_apply_of_mem r hr _ htmem,
    coefficientFamily_apply_on_rectangle hB r hrR hy]

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem cap_flow_initial_deriv_pos
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    0 < deriv (fun u => Y u t) s := by
  rw [(cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hs ht).deriv]
  exact Real.exp_pos _

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_ClosedSquareJetBounds
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.ODE

theorem modelSquare_closure_interior : closure (interior modelSquare) = modelSquare := by
  unfold modelSquare
  rw [← Set.pi_univ_Icc, interior_pi_set (Set.finite_univ : (Set.univ : Set (Fin 2)).Finite)]
  simp only [interior_Icc, closure_pi_set,
    closure_Ioo (by norm_num : (-3 : ℝ) ≠ 3), Set.pi_univ_Icc]

theorem CoordinateBound.restrict_domain {f : Coord → ℝ} {S T : Set Coord} {n : ℕ} {M : ℝ}
    (hf : CoordinateBound f S n M) (hTS : T ⊆ S) : CoordinateBound f T n M :=
  fun ds hds p hp => hf ds hds p (hTS hp)

theorem CoordinateBound.of_modelSquare_interior {f : Coord → ℝ} {U : Set Coord} {n : ℕ} {M : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hB : CoordinateBound f (interior modelSquare) n M) : CoordinateBound f modelSquare n M := by
  intro ds hds p hp
  have hcont : ContinuousOn (fun x => |iteratedCoordPartial ds f x|) modelSquare :=
    ((LowQuotient.iterated_contDiffOn hf hU ds).continuousOn.mono hSU).abs
  have hcl : p ∈ closure (interior modelSquare) := by rw [modelSquare_closure_interior]; exact hp
  apply le_on_closure (fun x hx => hB ds hds x hx) _ continuousOn_const hcl
  rw [modelSquare_closure_interior]
  exact hcont

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_NormedCoordinateCalculus
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Geometry
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {F : Coord → V} {U : Set Coord} {p : Coord}

theorem normed_second_coordPartial_eq_fderiv
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j F) p =
      fderiv ℝ (fderiv ℝ F) p (Pi.single i 1) (Pi.single j 1) := by
  have hs : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    (hs.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  unfold coordPartial
  rw [fderiv_clm_apply hd (differentiableAt_const (c := Pi.single j (1 : ℝ)))]
  simp

theorem normed_coordPartial_comm (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j F) p = coordPartial j (coordPartial i F) p := by
  rw [normed_second_coordPartial_eq_fderiv hF hU hp, normed_second_coordPartial_eq_fderiv hF hU hp]
  exact ((hF.contDiffAt (hU.mem_nhds hp)).isSymmSndFDerivAt
    (by
      simp only [minSmoothness, ite_eq_left (inferInstance : IsRCLikeNormedField ℝ)]
      exact WithTop.coe_le_coe.mpr le_top)) _ _

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_SixVariableDarboux
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

def stateBaseDomain (U : Set Coord) : Set DarbouxState := statePoint ⁻¹' U

def stateConnection (g : MetricField) (i j : Fin 2) (w : DarbouxState) : ℝ :=
  jetConnection g (statePoint w) i j (stateGradient w)

def stateMixed (g : MetricField) (w : DarbouxState) : ℝ :=
  jetMixed g (statePoint w) (w 4) (stateGradient w)

def stateDenominator (g : MetricField) (w : DarbouxState) : ℝ :=
  jetYY g (statePoint w) (w 5) (stateGradient w)

def stateEnergy (g : MetricField) (w : DarbouxState) : ℝ :=
  jetEnergy g (statePoint w) (stateGradient w)

def stateNumerator (g : MetricField) (w : DarbouxState) : ℝ :=
  jetNumerator g (statePoint w) (w 4) (stateGradient w)

def darbouxStateDomain (g : MetricField) (U : Set Coord) : Set DarbouxState :=
  {w | statePoint w ∈ U ∧ stateDenominator g w ≠ 0}

theorem statePoint_contDiff : ContDiff ℝ ∞ statePoint := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ (0 : Fin 6)
  · exact contDiff_apply ℝ ℝ (1 : Fin 6)

theorem stateGradient_contDiff : ContDiff ℝ ∞ stateGradient := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ (2 : Fin 6)
  · exact contDiff_apply ℝ ℝ (3 : Fin 6)

theorem stateBaseDomain_isOpen {U : Set Coord} (hU : IsOpen U) :
    IsOpen (stateBaseDomain U) := hU.preimage statePoint_contDiff.continuous

variable {g : MetricField} {U : Set Coord}

theorem statePoint_solutionJet (z : Coord → ℝ) (p : Coord) :
    statePoint (solutionJet z p) = p := by
  ext i
  fin_cases i <;> rfl

theorem stateGradient_solutionJet (z : Coord → ℝ) (p : Coord) :
    stateGradient (solutionJet z p) = fun i => coordPartial i z p := by
  ext i
  fin_cases i <;> rfl

theorem stateDenominator_solutionJet (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    stateDenominator g (solutionJet z p) = covHessian g z p 1 1 := by
  unfold stateDenominator
  rw [statePoint_solutionJet, stateGradient_solutionJet]
  exact jetYY_at_height g p z

theorem sixVariableP_solutionJet (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    sixVariableP g (solutionJet z p) =
      solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p) := by
  unfold sixVariableP
  rw [statePoint_solutionJet, stateGradient_solutionJet]
  rfl

theorem solutionJet_contDiffOn {z : Coord → ℝ} (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (solutionJet z) U := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_apply ℝ ℝ 0 U
  · exact contDiffOn_apply ℝ ℝ 1 U
  · exact partial_contDiffOn hz hU 0
  · exact partial_contDiffOn hz hU 1
  · exact partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0
  · exact partial_contDiffOn (partial_contDiffOn hz hU 1) hU 1

theorem solutionJet_mem_domain (g : MetricField) (z : Coord → ℝ) {p : Coord}
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0) :
    solutionJet z p ∈ darbouxStateDomain g U := by
  constructor
  · simpa only [statePoint_solutionJet] using hp
  · simpa only [stateDenominator_solutionJet] using hyy

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

def solutionJetCurve (z : Coord → ℝ) (x : ℝ) : ℝ → DarbouxState :=
  fun y => solutionJet z ![x, y]

theorem solutionJetCurve_contDiffAt {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U) :
    ContDiffAt ℝ ∞ (solutionJetCurve z x) y :=
  ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).comp y
    (verticalPoint_contDiff x).contDiffAt

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

theorem iteratedDeriv_state_eval {f : ℝ → DarbouxState} {y : ℝ}
    (hf : ContDiffAt ℝ ∞ f y) (n : ℕ) (i : Fin 6) :
    (iteratedDeriv n f y) i = iteratedDeriv n (fun t => f t i) y := by
  let L : DarbouxState →L[ℝ] ℝ := ContinuousLinearMap.proj i
  symm
  change iteratedFDeriv ℝ n (L ∘ f) y (fun _ => 1) = L (iteratedDeriv n f y)
  rw [L.iteratedFDeriv_comp_left hf (WithTop.coe_le_coe.mpr le_top)]
  rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_SixVariableLinearization
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem sixVariableP_update_gradient (g : MetricField) (w : DarbouxState) (i : Fin 2) (t : ℝ) :
    sixVariableP g (Function.update w (gradientStateIndex i) t) =
      solvedDarboux g (statePoint w) (w 4) (w 5) (Function.update (stateGradient w) i t) := by
  have hp : statePoint (Function.update w (gradientStateIndex i) t) = statePoint w := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [gradientStateIndex, statePoint]
  have hv : stateGradient (Function.update w (gradientStateIndex i) t) =
      Function.update (stateGradient w) i t := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [gradientStateIndex, stateGradient]
  unfold sixVariableP
  rw [hp, hv]
  fin_cases i <;> simp [gradientStateIndex]

theorem sixVariableP_update_mixed (g : MetricField) (w : DarbouxState) (t : ℝ) :
    sixVariableP g (Function.update w 4 t) =
      solvedDarboux g (statePoint w) t (w 5) (stateGradient w) := by
  have hp : statePoint (Function.update w 4 t) = statePoint w := by
    ext j
    fin_cases j <;> simp [statePoint]
  have hv : stateGradient (Function.update w 4 t) = stateGradient w := by
    ext j
    fin_cases j <;> simp [stateGradient]
  unfold sixVariableP
  rw [hp, hv]
  simp

theorem sixVariableP_update_yy (g : MetricField) (w : DarbouxState) (t : ℝ) :
    sixVariableP g (Function.update w 5 t) =
      solvedDarboux g (statePoint w) (w 4) t (stateGradient w) := by
  have hp : statePoint (Function.update w 5 t) = statePoint w := by
    ext j
    fin_cases j <;> simp [statePoint]
  have hv : stateGradient (Function.update w 5 t) = stateGradient w := by
    ext j
    fin_cases j <;> simp [stateGradient]
  unfold sixVariableP
  rw [hp, hv]
  simp

theorem solvedDarboux_first_variables_differentiableAt (g : MetricField) (p u : Coord) (b c : ℝ)
    (hyy : jetYY g p c u ≠ 0) : DifferentiableAt ℝ (solvedDarboux g p b c) u := by
  have hd := (jetConnection_differentiableAt g p u 0 0).add
    ((jetNumerator_differentiableAt g p u b).mul ((jetYY_differentiableAt g p u c).inv hyy))
  exact hd

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

def darbouxFaaTerm (g : MetricField) (z : Coord → ℝ) (x y : ℝ)
    {ell : ℕ} (c : OrderedFinpartition ell) : ℝ :=
  iteratedFDeriv ℝ c.length (sixVariableP g) (solutionJetCurve z x y)
    (fun j => iteratedDeriv (c.partSize j) (solutionJetCurve z x) y)

def directLinearization (g : MetricField) (z u : Coord → ℝ) (p : Coord) : ℝ :=
  heightPFirst g z 0 p * coordPartial 0 u p + heightPFirst g z 1 p * coordPartial 1 u p +
    2 * hessianQuotient g z p * coordPartial 0 (coordPartial 1 u) p -
    ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) *
      coordPartial 1 (coordPartial 1 u) p

theorem fullBlockPartition_term (g : MetricField) (z : Coord → ℝ) (x y : ℝ)
    (ell : ℕ) (hell : 0 < ell) :
    darbouxFaaTerm g z x y (fullBlockPartition ell hell) =
      fderiv ℝ (sixVariableP g) (solutionJetCurve z x y)
        (iteratedDeriv ell (solutionJetCurve z x) y) := by
  exact iteratedFDeriv_one_apply (𝕜 := ℝ) (f := sixVariableP g)
    (x := solutionJetCurve z x y) (fun _ : Fin 1 => iteratedDeriv ell (solutionJetCurve z x) y)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedCoercivity
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def directedPrincipal (A : Coord → ℝ) (ell : ℕ) (epsilon : ℝ) (p : Coord) : ℝ :=
  -((ell : ℝ) + 1 / 2) * coordPartial 1 A p + epsilon * p 0 * coordPartial 0 A p / 2

def directedSResidual (B r : Coord → ℝ) (_ : ℕ) (epsilon : ℝ) (p : Coord) : ℝ :=
  (coordPartial 1 (coordinatePrimitive B) p + epsilon + epsilon * p 0 * B p) / 2 - r p

theorem directedSResidual_bound {B r : Coord → ℝ} {ell : ℕ} {epsilon R MI MB Mr : ℝ}
    {p : Coord} (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (hR : 0 ≤ R)
    (ht : |p 0| ≤ R) (hI : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI)
    (hB : |B p| ≤ MB) (hr : |r p| ≤ Mr) :
    |directedSResidual B r ell epsilon p| ≤ (MI + 1 + R * MB) / 2 + Mr := by
  have hMB : 0 ≤ MB := (abs_nonneg _).trans hB
  have hprod : |epsilon * p 0 * B p| ≤ R * MB := by
    rw [abs_mul, abs_mul, abs_of_nonneg heps]
    have het : epsilon * |p 0| ≤ R :=
      (mul_le_mul_of_nonneg_left ht heps).trans (by nlinarith)
    exact (mul_le_mul het hB (abs_nonneg _) hR)
  unfold directedSResidual
  calc
    _ ≤ |(coordPartial 1 (coordinatePrimitive B) p + epsilon + epsilon * p 0 * B p) / 2| +
        |r p| := abs_sub _ _
    _ = |coordPartial 1 (coordinatePrimitive B) p + epsilon + epsilon * p 0 * B p| / 2 +
        |r p| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ ((|coordPartial 1 (coordinatePrimitive B) p| + |epsilon|) +
        |epsilon * p 0 * B p|) / 2 + |r p| := by
      have hsum : |coordPartial 1 (coordinatePrimitive B) p + epsilon + epsilon * p 0 * B p| ≤
          (|coordPartial 1 (coordinatePrimitive B) p| + |epsilon|) + |epsilon * p 0 * B p| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      exact add_le_add (div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
    _ ≤ (MI + 1 + R * MB) / 2 + Mr := by rw [abs_of_nonneg heps]; linarith

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_ModelCoercivity
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem modelCurvature_partial (kappa : ℝ) (p : Coord) (i : Fin 2) :
    coordPartial i (modelCurvature kappa) p =
      if i = 0 then 2 * kappa * p 0 else -kappa * deriv modelProfile (p 1) := by
  have hx := hasFDerivAt_apply (𝕜 := ℝ) 0 p
  have hy := ((modelProfile_contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (p 1)).hasDerivAt).comp_hasFDerivAt
    p (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hd := ((hx.pow 2).sub hy).const_mul kappa
  simp only [Function.comp_def, Pi.sub_def] at hd
  change fderiv ℝ (fun q : Coord => kappa * ((q 0) ^ 2 - modelProfile (q 1))) p
    (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;> simp
  ring

theorem modelCurvature_partial_y_nonpos {kappa : ℝ} (hkappa : 0 ≤ kappa)
    {p : Coord} (hy : p 1 ≤ 1 / 50) : coordPartial 1 (modelCurvature kappa) p ≤ 0 := by
  rw [modelCurvature_partial]
  norm_num only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hkappa)
    (modelProfile_deriv_nonneg_lower_cap hy)

theorem modelCurvature_negative_y_slope {kappa : ℝ} (hkappa : 0 ≤ kappa)
    {p : Coord} (hy : p 1 ≤ -(3 / 4 : ℝ)) :
    3 * kappa / 2 ≤ -coordPartial 1 (modelCurvature kappa) p := by
  rw [modelCurvature_partial]
  rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
  have hm := mul_le_mul_of_nonneg_left (modelProfile_deriv_lower_three_quarters hy) hkappa
  nlinarith only [hm]

theorem model_geometric_principal_lower
    {kappa g0 G rho rhoMax epsilon R Mq q : ℝ} {p : Coord} (ell : ℕ)
    (hkappa : 0 < kappa) (hg0 : 0 < g0) (hG : g0 ≤ G)
    (hrho : 0 < rho) (hrhoMax : rho ≤ rhoMax) (heps : 0 < epsilon)
    (ht : |p 0| ≤ R) (hq : |q| ≤ Mq)
    (hsmall : epsilon * R * Mq ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hy : p 1 ≤ 1 / 50) (hK : |modelCurvature kappa p| ≤ kappa / 8) :
    modelCoercivityMargin g0 kappa rhoMax epsilon ell ≤
      G * (-(((ell : ℝ) + 1 / 2) / rho + epsilon * p 0 * q / 2) *
        coordPartial 1 (modelCurvature kappa) p + epsilon * kappa * (p 0) ^ 2) := by
  let beta : ℝ := (ell : ℝ) + 1 / 2
  let coef : ℝ := beta / rho + epsilon * p 0 * q / 2
  let amin : ℝ := beta / (2 * rhoMax)
  let base : ℝ := coef * (-coordPartial 1 (modelCurvature kappa) p) + epsilon * kappa * (p 0) ^ 2
  have hmax : 0 < rhoMax := hrho.trans_le hrhoMax
  have hbeta : 0 < beta := by dsimp [beta] <;> positivity
  have hamin : 0 < amin := by dsimp [amin] <;> positivity
  have hcoef : amin ≤ coef := directed_model_slope_lower ell hrho hrhoMax heps.le ht hq hsmall
  have hKy : 0 ≤ -coordPartial 1 (modelCurvature kappa) p :=
    neg_nonneg.mpr (modelCurvature_partial_y_nonpos hkappa.le hy)
  have hterm : 0 ≤ epsilon * kappa * (p 0) ^ 2 := by positivity
  have hbase : 0 ≤ base := by dsimp [base]; exact add_nonneg (mul_nonneg (hamin.le.trans hcoef) hKy) hterm
  have hlower : kappa * min (3 * beta / (4 * rhoMax)) (5 * epsilon / 16) ≤ base := by
    by_cases hylo : p 1 ≤ -(3 / 4 : ℝ)
    · have hslope := modelCurvature_negative_y_slope hkappa.le hylo
      calc
        _ ≤ kappa * (3 * beta / (4 * rhoMax)) := mul_le_mul_of_nonneg_left (min_le_left _ _) hkappa.le
        _ = amin * (3 * kappa / 2) := by dsimp [amin] <;> ring
        _ ≤ amin * (-coordPartial 1 (modelCurvature kappa) p) :=
          mul_le_mul_of_nonneg_left hslope hamin.le
        _ ≤ coef * (-coordPartial 1 (modelCurvature kappa) p) := mul_le_mul_of_nonneg_right hcoef hKy
        _ ≤ base := by dsimp [base] <;> linarith
    · have hxsq := modelCurvature_middle_xsq_lower hkappa (lt_of_not_ge hylo).le hy hK
      calc
        _ ≤ kappa * (5 * epsilon / 16) := mul_le_mul_of_nonneg_left (min_le_right _ _) hkappa.le
        _ = epsilon * kappa * (5 / 16) := by ring
        _ ≤ epsilon * kappa * (p 0) ^ 2 := mul_le_mul_of_nonneg_left hxsq (mul_pos heps hkappa).le
        _ ≤ base := by
          dsimp [base]
          have hn := mul_nonneg (hamin.le.trans hcoef) hKy
          linarith
  have hfirst := mul_le_mul_of_nonneg_left hlower hg0.le
  have hsecond := mul_le_mul_of_nonneg_right hG hbase
  unfold modelCoercivityMargin
  dsimp only [base, coef, beta] at hfirst hsecond
  nlinarith only [hfirst, hsecond]

end SmoothLocal.Model

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_ModelPrincipal
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Model
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem modelPrincipal_derivative_remainder_bound
    {G : Coord → ℝ} {p : Coord} (ell : ℕ) {epsilon R MG : ℝ}
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (ht : |p 0| ≤ R)
    (hGs : |coordPartial 1 G p| ≤ MG) (hGt : |coordPartial 0 G p| ≤ MG) :
    |-((ell : ℝ) + 1 / 2) * coordPartial 1 G p +
      epsilon * p 0 * coordPartial 0 G p / 2| ≤ modelPrincipalRemainderBound ell R MG := by
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have hMG : 0 ≤ MG := (abs_nonneg _).trans hGs
  have hbeta : 0 ≤ (ell : ℝ) + 1 / 2 := by positivity
  have hfirst : |-((ell : ℝ) + 1 / 2) * coordPartial 1 G p| ≤
      ((ell : ℝ) + 1 / 2) * MG := by
    rw [abs_mul, abs_neg, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left hGs hbeta
  have hprod : |epsilon * p 0 * coordPartial 0 G p| ≤ R * MG := by
    rw [abs_mul, abs_mul, abs_of_nonneg heps]
    have het : epsilon * |p 0| ≤ R :=
      (mul_le_mul_of_nonneg_left ht heps).trans (by nlinarith)
    exact mul_le_mul het hGt (abs_nonneg _) hR
  have hsecond : |epsilon * p 0 * coordPartial 0 G p / 2| ≤ R * MG / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right hprod (by norm_num)
  have hsum := (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  unfold modelPrincipalRemainderBound
  nlinarith only [hsum]

theorem modelPrincipal_radius_error
    {g0 kappa rhoMax epsilon R MG K : ℝ} (ell : ℕ)
    (hg0 : 0 < g0) (hkappa : 0 < kappa) (hrho : 0 < rhoMax) (heps : 0 < epsilon)
    (hR : 0 ≤ R) (hMG : 0 ≤ MG)
    (hK : |K| ≤ modelPrincipalRadius g0 kappa rhoMax epsilon R MG ell) :
    |K| * modelPrincipalRemainderBound ell R MG ≤
      modelCoercivityMargin g0 kappa rhoMax epsilon ell / 2 := by
  let mu := modelCoercivityMargin g0 kappa rhoMax epsilon ell
  let M := modelPrincipalRemainderBound ell R MG
  have hmu : 0 < mu := modelCoercivityMargin_pos ell hg0 hkappa hrho heps
  have hM : 0 ≤ M := modelPrincipalRemainderBound_nonneg ell hR hMG
  have hden : 0 < 2 * (M + 1) := by positivity
  have hK' : |K| ≤ mu / (2 * (M + 1)) := hK.trans (min_le_right _ _)
  calc
    _ ≤ mu / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right hK' hM
    _ ≤ mu / (2 * (M + 1)) * (M + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_pos hmu hden).le
    _ = mu / 2 := by field_simp [show M + 1 ≠ 0 by positivity]

end SmoothLocal.Model

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowCurvature
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

def capModelCurvature (kappa : ℝ) (Y : ℝ → ℝ → ℝ) : Coord → ℝ :=
  fun p => modelCurvature kappa (capChart Y p)

theorem capChart_eq_vec (Y : ℝ → ℝ → ℝ) (p : Coord) :
    capChart Y p = ![p 0, capFlowHeight Y p] := by
  ext i
  fin_cases i <;> simp [capChart_zero, capChart_one]

variable {Y : ℝ → ℝ → ℝ}

theorem capModelCurvature_contDiffOn (kappa : ℝ)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)) :
    ContDiffOn ℝ ∞ (capModelCurvature kappa Y) capChartDomain :=
  (modelCurvature_contDiff kappa).comp_contDiffOn (capChart_contDiffOn hY)

variable {q : Coord → ℝ}

theorem capChart_mem_modelSquare {p : Coord} (hp : p ∈ capChartDomain)
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) :
    capChart Y p ∈ modelSquare := by
  apply coordinatePoint_mem_modelSquare
  · exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
  · have hd := abs_le.mp hdisp
    exact ⟨by linarith [hp.2.1, hd.1], by linarith [hp.2.2, hd.2]⟩

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def capChartSigma (Y : ℝ → ℝ → ℝ) (p : Coord) : ℝ :=
  -coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p /
    (coordPartial 1 (capFlowHeight Y) p) ^ 3

def driftOperator (q a B C0 u : Coord → ℝ) (p : Coord) : ℝ :=
  coordinateDrift q (coordinateDrift q u) p + a p * coordPartial 1 (coordPartial 1 u) p +
    B p * coordinateDrift q u p + C0 p * coordPartial 1 u p

variable {Y : ℝ → ℝ → ℝ} {u q : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem coordinateDrift_contDiffOn (hq : ContDiffOn ℝ ∞ q U)
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (coordinateDrift q u) U :=
  (partial_contDiffOn hu hU 0).sub (hq.mul (partial_contDiffOn hu hU 1))

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowHeightCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def heightOriginalA (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  gaussianCurvature g p * darbouxG g z p

def heightOriginalB (g : MetricField) (z : Coord → ℝ) (ell : ℕ) (p : Coord) : ℝ :=
  -heightPFirst g z 0 p - 2 * (ell : ℝ) * coordPartial 1 (hessianQuotient g z) p

def heightOriginalC0 (g : MetricField) (z : Coord → ℝ) (ell : ℕ) (p : Coord) : ℝ :=
  coordinateDrift (hessianQuotient g z) (hessianQuotient g z) p -
    hessianQuotient g z p * heightPFirst g z 0 p - heightPFirst g z 1 p +
      (ell : ℝ) * coordPartial 1 (heightOriginalA g z) p

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

def ChainWord.total (w : ChainWord) : ℕ := ∑ i, w.order i

def ChainWord.Positive (w : ChainWord) : Prop := ∀ i, 0 < w.order i

def ChainWord.Bounded (w : ChainWord) (n : ℕ) : Prop := ∀ i, w.order i ≤ n

def chainTerm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (w : ChainWord) (t : ℝ) : ℝ :=
  iteratedFDeriv ℝ w.arity F (J t) (fun i => iteratedDeriv (w.order i) J t)

theorem chainTerm_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t) (w : ChainWord) :
    HasDerivAt (chainTerm F J w)
      (chainTerm F J w.prepend t + ∑ i, chainTerm F J (w.bump i) t) t := by
  have hJ0 : HasDerivAt J (iteratedDeriv 1 J t) t := by
    simpa using iteratedDeriv_hasDerivAt_infty hJ 0
  have houter := (hF.differentiableAt_iteratedFDeriv (m := w.arity)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl w.arity)).hasFDerivAt
    |>.comp_hasDerivAt t hJ0
  have h := houter.hasFDerivAt.continuousMultilinearMap_apply
    (fun i => (iteratedDeriv_hasDerivAt_infty hJ (w.order i)).hasFDerivAt)
    |>.hasDerivAt
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [chainTerm, ChainWord.prepend, ChainWord.bump,
    add_apply, ContinuousLinearMap.comp_apply,
    sum_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul,
    ContinuousMultilinearMap.apply_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change (iteratedFDeriv ℝ w.arity F (J t))
      (fun j => iteratedDeriv (Function.update w.order i (w.order i + 1) j) J t) =
    (iteratedFDeriv ℝ w.arity F (J t))
      (Function.update (fun j => iteratedDeriv (w.order j) J t) i (iteratedDeriv (w.order i + 1) J t))
  congr 1
  funext j
  by_cases hj : j = i
  · subst j; simp
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]

theorem ChainWord.prepend_positive {w : ChainWord} (hw : w.Positive) :
    w.prepend.Positive := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Nat.zero_lt_one
  · exact hw j

theorem ChainWord.bump_positive {w : ChainWord} (hw : w.Positive) (i : Fin w.arity) :
    (w.bump i).Positive := by
  change ∀ j : Fin w.arity, 0 < Function.update w.order i (w.order i + 1) j
  intro j
  by_cases hj : j = i
  · subst j; simp
  · rw [Function.update_of_ne hj]
    exact hw j

theorem ChainWord.prepend_total (w : ChainWord) : w.prepend.total = w.total + 1 := by
  change (∑ j : Fin (w.arity + 1), Fin.cons 1 w.order j) = (∑ j : Fin w.arity, w.order j) + 1
  simp [Fin.sum_univ_succ, Nat.add_comm]

theorem ChainWord.bump_total (w : ChainWord) (i : Fin w.arity) :
    (w.bump i).total = w.total + 1 := by
  classical
  have hi : i ∈ (Finset.univ : Finset (Fin w.arity)) := Finset.mem_univ i
  have hsum := Finset.sum_update_of_mem hi w.order (w.order i + 1)
  simp only [Finset.sdiff_singleton_eq_erase] at hsum
  change (∑ j : Fin w.arity, Function.update w.order i (w.order i + 1) j) =
    (∑ j : Fin w.arity, w.order j) + 1
  rw [hsum]
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin w.arity)) w.order hi
  omega

theorem ChainWord.prepend_bounded {w : ChainWord} {n : ℕ}
    (hn : 1 ≤ n) (hw : w.Bounded n) : w.prepend.Bounded n := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hn
  · exact hw j

theorem ChainWord.bump_bounded {w : ChainWord} {n : ℕ}
    (hw : w.Bounded n) (i : Fin w.arity) : (w.bump i).Bounded (n + 1) := by
  change ∀ j : Fin w.arity, Function.update w.order i (w.order i + 1) j ≤ n + 1
  intro j
  by_cases hj : j = i
  · subst j
    simpa [ChainWord.bump] using Nat.add_le_add_right (hw i) 1
  · rw [Function.update_of_ne hj]
    exact Nat.le_succ_of_le (hw j)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_ChainResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation

def ChainWord.single (n : ℕ) : ChainWord := ⟨1, ![n]⟩

def chainSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (ws : List ChainWord) (t : ℝ) : ℝ :=
  (ws.map (fun w => chainTerm F J w t)).sum

theorem chainSum_append
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (ws vs : List ChainWord) (t : ℝ) :
    chainSum F J (ws ++ vs) t = chainSum F J ws t + chainSum F J vs t := by
  simp [chainSum]

theorem chainSum_replicate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (w : ChainWord) (n : ℕ) (t : ℝ) :
    chainSum F J (List.replicate n w) t = (n : ℝ) * chainTerm F J w t := by
  simp [chainSum, nsmul_eq_mul]

theorem chainSum_children
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (w : ChainWord) (t : ℝ) :
    chainSum F J w.children t = chainTerm F J w.prepend t +
      ∑ i, chainTerm F J (w.bump i) t := by
  simp [chainSum, ChainWord.children, List.map_ofFn, List.sum_ofFn]

theorem chainSum_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t)
    (ws : List ChainWord) :
    HasDerivAt (chainSum F J ws) (chainSum F J (ws.flatMap ChainWord.children) t) t := by
  induction ws with
  | nil => convert hasDerivAt_const t (0 : ℝ) using 1 <;> rfl
  | cons w ws ih =>
    have hw := chainTerm_hasDerivAt hF hJ w
    rw [← chainSum_children] at hw
    convert hw.add ih using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
    rw [List.flatMap_cons, chainSum_append]

theorem ChainWord.children_properties {w v : ChainWord} {n : ℕ}
    (hn : 1 ≤ n) (hp : w.Positive) (hb : w.Bounded n) (hv : v ∈ w.children) :
    v.Positive ∧ v.total = w.total + 1 ∧ v.Bounded (n + 1) := by
  simp only [ChainWord.children, List.mem_cons, List.mem_ofFn] at hv
  rcases hv with rfl | ⟨i, rfl⟩
  · refine ⟨ChainWord.prepend_positive hp, w.prepend_total, ?_⟩
    exact ChainWord.prepend_bounded (by omega) (fun j => Nat.le_succ_of_le (hb j))
  · exact ⟨ChainWord.bump_positive hp i, w.bump_total i,
      ChainWord.bump_bounded hb i⟩

theorem topResidualWords_properties : ∀ m w, w ∈ topResidualWords m →
    w.Positive ∧ w.total = m + 3 ∧ w.Bounded (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro w hw
    simp only [topResidualWords, List.mem_singleton] at hw
    subst w
    refine ⟨?_, ?_, ?_⟩
    · change ∀ i : Fin 3, 0 < (![1, 1, 1] : Fin 3 → ℕ) i
      intro i; fin_cases i <;> (first | (simp; all_goals first | (norm_num; done) | rfl | decide) | (norm_num; done) | norm_num)
    · change (∑ i : Fin 3, (![1, 1, 1] : Fin 3 → ℕ) i) = 0 + 3
      first | (simp [Fin.sum_univ_succ]; all_goals first | (norm_num [Fin.sum_univ_succ]; done) | rfl | decide) | (norm_num [Fin.sum_univ_succ]; done) | norm_num [Fin.sum_univ_succ]
    · change ∀ i : Fin 3, (![1, 1, 1] : Fin 3 → ℕ) i ≤ 0 + 1
      intro i; fin_cases i <;> (first | (simp; all_goals first | (norm_num; done) | rfl | decide) | (norm_num; done) | norm_num)
  | succ m ih =>
    intro w hw
    change w ∈ ((topResidualWords m).flatMap ChainWord.children ++
      List.replicate (m + 3) (ChainWord.triple 1 1 (m + 2))) ++
      List.replicate (m + 3) (ChainWord.pair 2 (m + 2)) at hw
    rw [List.mem_append, List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    · obtain ⟨v, hv, hw⟩ := List.mem_flatMap.mp hw
      obtain ⟨hp, ht, hb⟩ := ih v hv
      obtain ⟨hwp, hwt, hwb⟩ := ChainWord.children_properties (by omega) hp hb hw
      refine ⟨hwp, ?_, ?_⟩
      · omega
      · simpa [Nat.add_assoc] using hwb
    · have he := List.eq_of_mem_replicate hw
      subst w
      refine ⟨?_, ?_, ?_⟩
      · change ∀ i : Fin 3, 0 < (![1, 1, m + 2] : Fin 3 → ℕ) i
        intro i; fin_cases i <;> simp
      · change (∑ i : Fin 3, (![1, 1, m + 2] : Fin 3 → ℕ) i) = m + 1 + 3
        simp [Fin.sum_univ_succ]; omega
      · change ∀ i : Fin 3, (![1, 1, m + 2] : Fin 3 → ℕ) i ≤ m + 1 + 1
        intro i; fin_cases i <;> simp
    · have he := List.eq_of_mem_replicate hw
      subst w
      refine ⟨?_, ?_, ?_⟩
      · change ∀ i : Fin 2, 0 < (![2, m + 2] : Fin 2 → ℕ) i
        intro i; fin_cases i <;> simp
      · change (∑ i : Fin 2, (![2, m + 2] : Fin 2 → ℕ) i) = m + 1 + 3
        simp [Fin.sum_univ_succ]; omega
      · change ∀ i : Fin 2, (![2, m + 2] : Fin 2 → ℕ) i ≤ m + 1 + 1
        intro i; fin_cases i <;> simp

theorem topResidualWords_sum_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (m : ℕ) (t : ℝ) :
    chainSum F J (topResidualWords (m + 1)) t =
      chainSum F J ((topResidualWords m).flatMap ChainWord.children) t +
      (m + 3 : ℝ) * chainTerm F J (ChainWord.triple 1 1 (m + 2)) t +
      (m + 3 : ℝ) * chainTerm F J (ChainWord.pair 2 (m + 2)) t := by
  simp only [topResidualWords, chainSum_append, chainSum_replicate, Nat.cast_add,
    Nat.cast_ofNat, add_assoc]

theorem topResidual_high_unique {m : ℕ} (hm : 8 ≤ m + 3)
    {w : ChainWord} (hw : w ∈ topResidualWords m) (base : Fin w.arity → ℕ)
    (hb : ∀ i, base i ≤ 2) {i j : Fin w.arity}
    (hi : m + 2 ≤ w.order i + base i) (hj : m + 2 ≤ w.order j + base j) : i = j := by
  classical
  by_contra hij
  have hsum := (topResidualWords_properties m w hw).2.1
  have hpair : w.order i + w.order j ≤ w.total := by
    have hh : ∑ k ∈ ({i, j} : Finset (Fin w.arity)), w.order k ≤ ∑ k, w.order k :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    simpa [ChainWord.total, Finset.sum_pair hij] using hh
  have hbi := hb i
  have hbj := hb j
  omega

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TopChainExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation

theorem ChainWord.prepend_single (n : ℕ) :
    (ChainWord.single n).prepend = ChainWord.pair 1 n := rfl

theorem ChainWord.bump_single (n : ℕ) :
    (ChainWord.single n).bump (0 : Fin 1) = ChainWord.single (n + 1) := by
  change ChainWord.mk 1 _ = ChainWord.mk 1 _
  congr 1
  ext i
  fin_cases i
  simp [ChainWord.single]

theorem ChainWord.prepend_pair (a b : ℕ) :
    (ChainWord.pair a b).prepend = ChainWord.triple 1 a b := rfl

theorem ChainWord.bump_pair_zero (a b : ℕ) :
    (ChainWord.pair a b).bump (0 : Fin 2) = ChainWord.pair (a + 1) b := by
  apply congrArg (ChainWord.mk 2)
  change Function.update (![a, b] : Fin 2 → ℕ) (0 : Fin 2) (a + 1) = ![a + 1, b]
  funext i
  fin_cases i <;> simp

theorem ChainWord.bump_pair_one (a b : ℕ) :
    (ChainWord.pair a b).bump (1 : Fin 2) = ChainWord.pair a (b + 1) := by
  change ChainWord.mk 2 _ = ChainWord.mk 2 _
  congr 1
  ext i
  fin_cases i <;> simp [ChainWord.pair]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem chainTerm_single_eq (F : E → ℝ) (J : ℝ → E) (n : ℕ) (t : ℝ) :
    chainTerm F J (ChainWord.single n) t =
      fderiv ℝ F (J t) (iteratedDeriv n J t) := by
  simp only [chainTerm, ChainWord.single, Matrix.cons_val_fin_one]
  exact iteratedFDeriv_one_apply (𝕜 := ℝ) (f := F) (x := J t)
    (fun _ : Fin 1 => iteratedDeriv n J t)

theorem chainTerm_pair_eq (F : E → ℝ) (J : ℝ → E) (a b : ℕ) (t : ℝ) :
    chainTerm F J (ChainWord.pair a b) t =
      iteratedFDeriv ℝ 2 F (J t) ![iteratedDeriv a J t, iteratedDeriv b J t] := by
  apply congrArg (iteratedFDeriv ℝ 2 F (J t))
  ext i
  fin_cases i <;> rfl

theorem chainTerm_triple_eq (F : E → ℝ) (J : ℝ → E) (a b c : ℕ) (t : ℝ) :
    chainTerm F J (ChainWord.triple a b c) t =
      iteratedFDeriv ℝ 3 F (J t)
        ![iteratedDeriv a J t, iteratedDeriv b J t, iteratedDeriv c J t] := by
  apply congrArg (iteratedFDeriv ℝ 3 F (J t))
  ext i
  fin_cases i <;> rfl

theorem chainTerm_pair_symm {F : E → ℝ} (J : ℝ → E) {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (a b : ℕ) :
    chainTerm F J (ChainWord.pair a b) t = chainTerm F J (ChainWord.pair b a) t := by
  rw [chainTerm_pair_eq, chainTerm_pair_eq]
  have hs := hF.isSymmSndFDerivAt (by
    simp only [minSmoothness, ite_eq_left (inferInstance : IsRCLikeNormedField ℝ)]
    exact WithTop.coe_le_coe.mpr le_top)
  exact hs.iteratedFDeriv_cons

theorem chainTerm_single_hasDerivAt {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t) (n : ℕ) :
    HasDerivAt (chainTerm F J (ChainWord.single n))
      (chainTerm F J (ChainWord.single (n + 1)) t +
        chainTerm F J (ChainWord.pair 1 n) t) t := by
  have h := chainTerm_hasDerivAt hF hJ (ChainWord.single n)
  change HasDerivAt _
    (chainTerm F J (ChainWord.single n).prepend t +
      ∑ i : Fin 1, chainTerm F J ((ChainWord.single n).bump i) t) t at h
  simpa only [Fin.sum_univ_one, ChainWord.prepend_single, ChainWord.bump_single,
    add_comm] using h

theorem chainTerm_pair_hasDerivAt {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t) (a b : ℕ) :
    HasDerivAt (chainTerm F J (ChainWord.pair a b))
      (chainTerm F J (ChainWord.triple 1 a b) t +
        chainTerm F J (ChainWord.pair (a + 1) b) t +
        chainTerm F J (ChainWord.pair a (b + 1)) t) t := by
  have h := chainTerm_hasDerivAt hF hJ (ChainWord.pair a b)
  change HasDerivAt _
    (chainTerm F J (ChainWord.pair a b).prepend t +
      ∑ i : Fin 2, chainTerm F J ((ChainWord.pair a b).bump i) t) t at h
  simpa only [Fin.sum_univ_two, ChainWord.prepend_pair, ChainWord.bump_pair_zero,
    ChainWord.bump_pair_one, add_assoc] using h

theorem top_chain_three {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t) :
    iteratedDeriv 3 (F ∘ J) t =
      chainTerm F J (ChainWord.single 3) t +
        3 * chainTerm F J (ChainWord.pair 1 2) t +
        chainSum F J (topResidualWords 0) t := by
  have h := iteratedDeriv_vcomp_three
    (hF.of_le (WithTop.coe_le_coe.mpr le_top))
    (hJ.of_le (WithTop.coe_le_coe.mpr le_top))
  have heq : iteratedDeriv 3 (F ∘ J) t =
      chainTerm F J (ChainWord.triple 1 1 1) t +
      chainTerm F J (ChainWord.pair 2 1) t +
      2 * chainTerm F J (ChainWord.pair 1 2) t +
      chainTerm F J (ChainWord.single 3) t := by
    rw [chainTerm_triple_eq, chainTerm_pair_eq, chainTerm_pair_eq, chainTerm_single_eq]
    simp only [iteratedDeriv_one, two_smul, two_mul] at h ⊢
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    have hv : (![deriv J t, deriv J t, deriv J t] : Fin 3 → E) = fun _ => deriv J t := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
  rw [chainTerm_pair_symm J hF 2 1] at heq
  simp only [topResidualWords, chainSum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  linarith [heq]

theorem top_chain_expansion
    {F : E → ℝ} {J : ℝ → E} {O : Set E} {I : Set ℝ}
    (hO : IsOpen O) (hI : IsOpen I) (hF : ContDiffOn ℝ ∞ F O)
    (hJ : ContDiffOn ℝ ∞ J I) (hmap : MapsTo J I O) :
    ∀ m t, t ∈ I →
      iteratedDeriv (m + 3) (F ∘ J) t =
        chainTerm F J (ChainWord.single (m + 3)) t +
          (m + 3 : ℝ) * chainTerm F J (ChainWord.pair 1 (m + 2)) t +
          chainSum F J (topResidualWords m) t := by
  intro m
  induction m with
  | zero =>
    intro t ht
    simpa only [Nat.zero_add, Nat.cast_zero, zero_add] using top_chain_three (hF.contDiffAt (hO.mem_nhds (hmap ht)))
      (hJ.contDiffAt (hI.mem_nhds ht))
  | succ m ih =>
    intro t ht
    have hFt := hF.contDiffAt (hO.mem_nhds (hmap ht))
    have hJt := hJ.contDiffAt (hI.mem_nhds ht)
    have heq : iteratedDeriv (m + 3) (F ∘ J) =ᶠ[𝓝 t]
        (fun r => chainTerm F J (ChainWord.single (m + 3)) r +
          (m + 3 : ℝ) * chainTerm F J (ChainWord.pair 1 (m + 2)) r +
          chainSum F J (topResidualWords m) r) := by
      filter_upwards [hI.mem_nhds ht] with r hr
      exact ih r hr
    have hd := ((chainTerm_single_hasDerivAt hFt hJt (m + 3)).add
      ((chainTerm_pair_hasDerivAt hFt hJt 1 (m + 2)).const_mul (m + 3 : ℝ))).add
      (chainSum_hasDerivAt hFt hJt (topResidualWords m))
    have hd' := hd.deriv
    change deriv (fun r => chainTerm F J (ChainWord.single (m + 3)) r +
      (m + 3 : ℝ) * chainTerm F J (ChainWord.pair 1 (m + 2)) r +
      chainSum F J (topResidualWords m) r) t = _ at hd'
    rw [show m + 1 + 3 = (m + 3) + 1 by omega, iteratedDeriv_succ, heq.deriv_eq, hd']
    rw [topResidualWords_sum_succ]
    simp only [Nat.cast_add, Nat.add_assoc, Nat.reduceAdd]
    ring

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_SecondJetExtraction
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem second_fderiv_comp_constant_direction
    {F : DarbouxState → ℝ} {J : Coord → DarbouxState} {p : Coord}
    (hF : ContDiffAt ℝ ∞ F (J p)) (hJ : DifferentiableAt ℝ J p) (v : DarbouxState) :
    iteratedFDeriv ℝ 2 F (J p) ![coordPartial 1 J p, v] =
      coordPartial 1 (fun r => fderiv ℝ F (J r) v) p := by
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) (J p) :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun r => fderiv ℝ F (J r)) p := hdF.comp p hJ
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold coordPartial
  have hcomp : fderiv ℝ (fun r => fderiv ℝ F (J r)) p =
      (fderiv ℝ (fderiv ℝ F) (J p)).comp (fderiv ℝ J p) := by
    convert fderiv_comp p hdF hJ using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  rw [fderiv_clm_apply hc (differentiableAt_const (c := v)), hcomp]
  simp

def secondJetCorrection (g : MetricField) (z u : Coord → ℝ) (p : Coord) : ℝ :=
  2 * coordPartial 1 (hessianQuotient g z) p * coordPartial 0 u p -
  coordPartial 1 (fun r => (hessianQuotient g z r)^2 +
    gaussianCurvature g r * darbouxG g z r) p * coordPartial 1 u p

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_ScalarChainExpansion
attribute [-simp] _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem finite_state_basis_decomposition (v : DarbouxState) :
    v = ∑ i : Fin 6, v i • (Pi.single i (1 : ℝ) : DarbouxState) := by
  ext j
  simp [Pi.single_apply, Finset.sum_apply, smul_eq_mul]

theorem multilinear_state_components {k : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin k => DarbouxState) ℝ)
    (v : Fin k → DarbouxState) :
    L v = ∑ r : Fin k → Fin 6,
      L (fun i => Pi.single (r i) (1 : ℝ)) * ∏ i, v i (r i) := by
  classical
  calc
    L v = L (fun i => ∑ j : Fin 6, v i j • (Pi.single j (1 : ℝ) : DarbouxState)) := by
      congr 1
      funext i
      exact finite_state_basis_decomposition (v i)
    _ = ∑ r : Fin k → Fin 6, L (fun i => v i (r i) • Pi.single (r i) (1 : ℝ)) :=
      L.map_sum (fun i j => v i j • (Pi.single j (1 : ℝ) : DarbouxState))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [L.map_smul_univ]
      simp only [smul_eq_mul, mul_comm]

def coordinateChainCoefficient (g : MetricField) (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p)
    (fun i => Pi.single (r i) (1 : ℝ))

def coordinateChainFactor (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (i : Fin w.arity) (p : Coord) : ℝ :=
  verticalJet (solutionJet z) (w.order i) p (r i)

def chainFactorOrder (w : ChainWord) (r : Fin w.arity → Fin 6) (i : Fin w.arity) : ℕ :=
  w.order i + stateBaseOrder (r i)

theorem coordinateChainTerm_scalar_expansion (g : MetricField) (z : Coord → ℝ)
    (w : ChainWord) (p : Coord) :
    coordinateChainTerm g z w p =
      ∑ r : Fin w.arity → Fin 6,
        coordinateChainCoefficient g z w r p * ∏ i, coordinateChainFactor z w r i p :=
  multilinear_state_components _ _

theorem ChainWord.arity_le_total {w : ChainWord} (hw : w.Positive) : w.arity ≤ w.total := by
  have hsum : ∑ _i : Fin w.arity, (1 : ℕ) ≤ ∑ i : Fin w.arity, w.order i :=
    Finset.sum_le_sum (fun index _ => hw index)
  simpa [ChainWord.total] using hsum

theorem residual_scalar_factor_orders {m : ℕ} {w : ChainWord}
    (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) :
    (∀ i, chainFactorOrder w r i ≤ m + 3) ∧ w.arity ≤ m + 3 := by
  obtain ⟨hp, ht, hb⟩ := topResidualWords_properties m w hw
  constructor
  · intro i
    have hi := hb i
    have hr := stateBaseOrder_le_two (r i)
    unfold chainFactorOrder
    omega
  · exact ht ▸ ChainWord.arity_le_total hp

theorem residual_scalar_high_unique {m : ℕ} (hm : 8 ≤ m + 3) {w : ChainWord}
    (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) {i j : Fin w.arity}
    (hi : m + 2 ≤ chainFactorOrder w r i) (hj : m + 2 ≤ chainFactorOrder w r j) : i = j :=
  topResidual_high_unique hm hw (fun k => stateBaseOrder (r k))
    (fun k => stateBaseOrder_le_two (r k)) hi hj

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_MixedCoordinateCalculus
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem orderedPartial_append
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ds es : List (Fin 2)) (f : Coord → E) :
    iteratedCoordPartial (ds ++ es) f = iteratedCoordPartial ds (iteratedCoordPartial es f) := by
  induction ds with
  | nil => rfl
  | cons i ds ih => simp only [List.cons_append, iteratedCoordPartial, ih]

theorem fullJet_coordinate_inputs_eq_ordered
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord → E} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (n : ℕ) (d : Fin n → Fin 2) {p : Coord} (hp : p ∈ U) :
    iteratedFDeriv ℝ n f p (fun i => Pi.single (d i) (1 : ℝ)) =
      iteratedCoordPartial (List.ofFn d) f p := by
  induction n generalizing p with
  | zero => simp [iteratedCoordPartial]
  | succ n ih =>
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
      rw [hd.iteratedFDeriv_succ_apply_left']
      have he : (fun q => iteratedFDeriv ℝ n f q
          (fun i => Pi.single (d i.succ) (1 : ℝ))) =ᶠ[𝓝 p]
          iteratedCoordPartial (List.ofFn (fun i => d i.succ)) f := by
        filter_upwards [hU.mem_nhds hp] with q hq
        exact ih (fun i => d i.succ) hq
      change fderiv ℝ (fun q => iteratedFDeriv ℝ n f q
        (fun i => Pi.single (d i.succ) (1 : ℝ))) p (Pi.single (d 0) 1) = _
      rw [he.fderiv_eq, List.ofFn_succ]
      rfl

theorem state_fullJet_eval
    {f : Coord → DarbouxState} {p : Coord} (hf : ContDiffAt ℝ ∞ f p)
    (n : ℕ) (v : Fin n → Coord) (i : Fin 6) :
    (iteratedFDeriv ℝ n f p v) i = iteratedFDeriv ℝ n (fun q => f q i) p v := by
  let L : DarbouxState →L[ℝ] ℝ := ContinuousLinearMap.proj i
  symm
  change iteratedFDeriv ℝ n (L ∘ f) p v = L (iteratedFDeriv ℝ n f p v)
  rw [L.iteratedFDeriv_comp_left hf (WithTop.coe_le_coe.mpr le_top)]
  rfl

theorem solutionJet_fullJet_ge_two
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (n : ℕ) (hn : 2 ≤ n) (v : Fin n → Coord) :
    iteratedFDeriv ℝ n (solutionJet z) p v =
      ![0, 0, iteratedFDeriv ℝ n (coordPartial 0 z) p v,
        iteratedFDeriv ℝ n (coordPartial 1 z) p v,
        iteratedFDeriv ℝ n (coordPartial 0 (coordPartial 1 z)) p v,
        iteratedFDeriv ℝ n (coordPartial 1 (coordPartial 1 z)) p v] := by
  have hJ := (solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)
  ext i
  rw [state_fullJet_eval hJ n v i]
  fin_cases i
  · exact fullJet_linear_zero (ContinuousLinearMap.proj 0 : Coord →L[ℝ] ℝ) hn p v
  · exact fullJet_linear_zero (ContinuousLinearMap.proj 1 : Coord →L[ℝ] ℝ) hn p v
  · rfl
  · rfl
  · rfl
  · rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_CoordinateJetReverseNorm
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem full_jet_norm_le_coordinate_words {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hword : ∀ ds : List (Fin 2), ds.length = n → |iteratedCoordPartial ds f p| ≤ B) :
    ‖iteratedFDeriv ℝ n f p‖ ≤ (2 : ℝ)^n * B := by
  apply multilinear_norm_le_coordinate_bound _ hB
  intro r
  rw [fullJet_coordinate_inputs_eq_ordered hf hU n r hp, Real.norm_eq_abs]
  exact hword (List.ofFn r) (by simp)

theorem CoordinateBound.full_jet_norm_bound {f : Coord → ℝ} {U S : Set Coord}
    {N n : ℕ} {B : ℝ} (h : CoordinateBound f S N B)
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hSU : S ⊆ U) (hB : 0 ≤ B)
    (hn : n ≤ N) {p : Coord} (hp : p ∈ S) :
    ‖iteratedFDeriv ℝ n f p‖ ≤ (2 : ℝ)^n * B := by
  apply full_jet_norm_le_coordinate_words hf hU (hSU hp) n hB
  intro ds hds
  exact h ds (by omega) p hp

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

theorem cap_flow_strictMonoOn_initial
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    StrictMonoOn (fun s => Y s t) (Ioo (-2 : ℝ) 2) := by
  have hc : ContinuousOn (fun s => Y s t) (Ioo (-2 : ℝ) 2) :=
    HasDerivAt.continuousOn
      (fun s hs => cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hs ht)
  apply strictMonoOn_of_deriv_pos (convex_Ioo (-2 : ℝ) 2) hc
  intro s hs
  apply cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode _ ht
  simpa only [interior_Ioo] using hs

theorem triangularFlow_injOn
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) :
    InjOn (triangularFlow Y) (pairRectangle 2 (-2) 2) := by
  intro p hp z hz he
  have ht : p.1 = z.1 := by
    simpa only [triangularFlow] using congrArg (fun v : ℝ × ℝ => v.1) he
  have hy : Y p.2 p.1 = Y z.2 z.1 := by
    simpa only [triangularFlow] using congrArg (fun v : ℝ × ℝ => v.2) he
  rw [ht] at hy
  exact Prod.ext ht
    ((cap_flow_strictMonoOn_initial hq hU hSU hY hrange hstart hode hz.1).injOn hp.2 hz.2 hy)

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowInverse
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem triangularFlow_hasFDerivAt_equiv
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {p : ℝ × ℝ} (hp : p ∈ pairRectangle 2 (-2) 2) :
    ∃ A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), HasFDerivAt (triangularFlow Y) (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
  let F (v : ℝ × ℝ) := Y v.2 v.1
  let a := -q (coordinatePoint p.1 (Y p.2 p.1))
  let b := Real.exp (-(∫ r in 0..p.1, coordPartial 1 q (coordinatePoint r (Y p.2 r))))
  have hF : ContDiffOn ℝ ∞ F (pairRectangle 2 (-2) 2) :=
    cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hd := ((hF.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hdx : HasDerivAt (fun t => F (t, p.2)) a p.1 :=
    (hode p.2 ⟨hp.2.1.le, hp.2.2.le⟩ p.1 ⟨hp.1.1.le, hp.1.2.le⟩).hasDerivAt
      (Icc_mem_nhds hp.1.1 hp.1.2)
  have hdy : HasDerivAt (fun s => F (p.1, s)) b p.2 :=
    cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hp.2 hp.1
  have hdx' : HasDerivAt (fun t => F (t, p.2)) (fderiv ℝ F p (1, 0)) p.1 := by
    convert hd.comp_hasDerivAt p.1 ((hasDerivAt_id p.1).prodMk
      (hasDerivAt_const p.1 p.2)) using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hdy' : HasDerivAt (fun s => F (p.1, s)) (fderiv ℝ F p (0, 1)) p.2 := by
    convert hd.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk
      (hasDerivAt_id p.2)) using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hx : fderiv ℝ F p (1, 0) = a := hdx'.unique hdx
  have hy : fderiv ℝ F p (0, 1) = b := hdy'.unique hdy
  have hdeq : fderiv ℝ F p = jointDifferential a b := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = v.1 • ((1, 0) : ℝ × ℝ) + v.2 • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    calc
      fderiv ℝ F p v = v.1 * a + v.2 * b := by
        conv_lhs => rw [hv]
        simp only [map_add, map_smul, smul_eq_mul, hx, hy]
      _ = jointDifferential a b v := by simp [jointDifferential]
  have hFD : HasFDerivAt F (jointDifferential a b) p := hd.congr_fderiv hdeq
  have hb : b ≠ 0 := (Real.exp_pos _).ne'
  refine ⟨triangularLinearEquiv a b hb, ?_⟩
  have hTF := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk hFD
  convert hTF using 1 <;> first
    | rfl
    | (ext <;> simp [triangularLinearEquiv, jointDifferential])

theorem exists_triangularFlow_smooth_chart
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {p : ℝ × ℝ} (hp : p ∈ pairRectangle 2 (-2) 2) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      p ∈ e.source ∧ e.source ⊆ pairRectangle 2 (-2) 2 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let D := pairRectangle 2 (-2) 2
  have hD : IsOpen D := pairRectangle_isOpen 2 (-2) 2
  have hTF : ContDiffOn ℝ ∞ (triangularFlow Y) D :=
    contDiffOn_fst.prodMk (cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode)
  have hTFp := hTF.contDiffAt (hD.mem_nhds hp)
  obtain ⟨A, hA⟩ := triangularFlow_hasFDerivAt_equiv hq hU hSU hY hrange hstart hode hp
  let e0 := hTFp.toOpenPartialHomeomorph (triangularFlow Y) hA (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let e := e0.restrOpen D hD
  have heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y := rfl
  have hsub : e.source ⊆ D := fun _ hx => hx.2
  refine ⟨e, ⟨hTFp.mem_toOpenPartialHomeomorph_source hA (by simp), hp⟩,
    hsub, heq, ?_, ?_⟩
  · rw [heq]
    exact hTF.mono hsub
  · intro y hy
    have hx : e.symm y ∈ D := hsub (e.map_target hy)
    obtain ⟨L, hL⟩ := triangularFlow_hasFDerivAt_equiv hq hU hSU hY hrange hstart hode hx
    have hLe : HasFDerivAt e (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (e.symm y) := by
      rw [heq]
      exact hL
    have hfe : ContDiffAt ℝ ∞ e (e.symm y) := by
      rw [heq]
      exact hTF.contDiffAt (hD.mem_nhds hx)
    exact (e.contDiffAt_symm hy hLe hfe).contDiffWithinAt

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowChart
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

theorem exists_global_triangularFlow_chart
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      e.source = pairRectangle 2 (-2) 2 ∧
      e.target = triangularFlow Y '' pairRectangle 2 (-2) 2 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let D := pairRectangle 2 (-2) 2
  have hD : IsOpen D := pairRectangle_isOpen 2 (-2) 2
  have hTF : ContDiffOn ℝ ∞ (triangularFlow Y) D :=
    contDiffOn_fst.prodMk (cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode)
  have hinj : InjOn (triangularFlow Y) D := triangularFlow_injOn hq hU hSU hY hrange hstart hode
  have hlocal : IsLocalHomeomorphOn (triangularFlow Y) D := by
    intro x hx
    obtain ⟨e, he, hsub, heq, hf, hi⟩ :=
      exists_triangularFlow_smooth_chart hq hU hSU hY hrange hstart hode hx
    exact ⟨e, he, heq.symm⟩
  have hopen : IsOpenMap (D.domRestrict (triangularFlow Y)) := by
    apply IsOpenMap.of_nhds_le
    intro x
    have he : (𝓝 x).map (D.domRestrict (triangularFlow Y)) =
        𝓝 (triangularFlow Y x) := by
      change (𝓝 x).map ((triangularFlow Y) ∘ (Subtype.val : D → ℝ × ℝ)) = _
      rw [← Filter.map_map, hD.isOpenEmbedding_subtypeVal.map_nhds_eq,
        hlocal.map_nhds_eq x.2]
    exact he.ge
  let pe := hinj.toPartialEquiv (triangularFlow Y) D
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict pe hTF.continuousOn hopen hD
  have heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y := rfl
  have hsource : e.source = D := rfl
  refine ⟨e, hsource, rfl, heq, ?_, ?_⟩
  · rw [heq, hsource]
    exact hTF
  · intro y hy
    have hx : e.symm y ∈ D := by
      rw [← hsource]
      exact e.map_target hy
    obtain ⟨A, hA⟩ := triangularFlow_hasFDerivAt_equiv hq hU hSU hY hrange hstart hode hx
    have hAe : HasFDerivAt e (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (e.symm y) := by
      rw [heq]
      exact hA
    have hfe : ContDiffAt ℝ ∞ e (e.symm y) := by
      rw [heq]
      exact hTF.contDiffAt (hD.mem_nhds hx)
    exact (e.contDiffAt_symm hy hAe hfe).contDiffWithinAt

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem capChart_injOn_of_pairChart
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y) :
    InjOn (capChart Y) capChartDomain := by
  intro p hp r hr hsame
  have hp' : (p 0,p 1) ∈ e.source := by rw [hsource]; exact hp
  have hr' : (r 0,r 1) ∈ e.source := by rw [hsource]; exact hr
  have hpair : e (p 0,p 1) = e (r 0,r 1) := by
    rw [heq]
    apply Prod.ext
    · simpa only [triangularFlow,capChart_zero] using congrArg (fun q : Coord => q 0) hsame
    · simpa only [triangularFlow,capChart_one,capFlowHeight] using congrArg (fun q : Coord => q 1) hsame
  have hinj := e.injOn hp' hr' hpair
  ext i
  fin_cases i
  · exact congrArg Prod.fst hinj
  · exact congrArg Prod.snd hinj

end SmoothLocal.Flow

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

theorem elliptic_ratio_scalar
    {d D c Cv M v vt vs A As B C : ℝ}
    (hd : 0 < d) (hdD : d ≤ D) (hc : 0 < c) (hCv : 0 ≤ Cv) (hM : 0 ≤ M)
    (hv : 0 < v) (hvd : v ≤ d ^ 6)
    (hvt : |vt| ≤ Cv * Real.sqrt v * (d ^ 2 + d ^ 3))
    (hvs : |vs| ≤ Cv * Real.sqrt v * (d ^ 2 + d ^ 3))
    (hAlo : c * d ≤ A) (hAhi : |A| ≤ M)
    (hAs : |As| ≤ M) (hB : |B| ≤ M) (hC : |C| ≤ M) :
    (vt - v * B) ^ 2 / v + (As * v + A * vs - v * C) ^ 2 / (A * v) ≤
      ellipticRatioConstant D c Cv M := by
  have hD : 0 ≤ D := hd.le.trans hdD
  have hA : 0 < A := (mul_pos hc hd).trans_le hAlo
  have hAM : A ≤ M := (le_abs_self A).trans hAhi
  let W : ℝ := Cv ^ 2 * (d ^ 2 + d ^ 3) ^ 2
  have hW : 0 ≤ W := mul_nonneg (pow_nonneg hCv 2) (sq_nonneg _)
  have hvt2 : vt ^ 2 ≤ v * W := by
    calc
      vt ^ 2 ≤ (Cv * Real.sqrt v * (d ^ 2 + d ^ 3)) ^ 2 :=
        square_bound_of_abs_bound hvt
      _ = Cv ^ 2 * (Real.sqrt v) ^ 2 * (d ^ 2 + d ^ 3) ^ 2 := by ring
      _ = v * W := by rw [Real.sq_sqrt hv.le]; dsimp [W] <;> ring
  have hvs2 : vs ^ 2 ≤ v * W := by
    calc
      vs ^ 2 ≤ (Cv * Real.sqrt v * (d ^ 2 + d ^ 3)) ^ 2 :=
        square_bound_of_abs_bound hvs
      _ = Cv ^ 2 * (Real.sqrt v) ^ 2 * (d ^ 2 + d ^ 3) ^ 2 := by ring
      _ = v * W := by rw [Real.sq_sqrt hv.le]; dsimp [W] <;> ring
  have hB2 := square_bound_of_abs_bound hB
  have hb : |As - C| ≤ 2 * M := by
    calc
      |As - C| ≤ |As| + |C| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le As 0 C
      _ ≤ M + M := add_le_add hAs hC
      _ = 2 * M := by ring
  have hb2 : (As - C) ^ 2 ≤ 4 * M ^ 2 := by
    nlinarith only [square_bound_of_abs_bound hb]
  have ht : (vt - v * B) ^ 2 / v ≤ 2 * W + 2 * v * M ^ 2 := by
    apply (div_le_iff₀ hv).2
    have hBv := mul_le_mul_of_nonneg_left hB2 (sq_nonneg v)
    nlinarith only [hvt2, hBv, sq_nonneg (vt + v * B)]
  have hvsdiv : vs ^ 2 / v ≤ W := (div_le_iff₀ hv).2 (by nlinarith only [hvs2])
  have hsum : (As * v + A * vs - v * C) ^ 2 ≤
      2 * (A * vs) ^ 2 + 2 * (v * (As - C)) ^ 2 := by
    nlinarith only [sq_nonneg (A * vs - v * (As - C))]
  have hsraw : (As * v + A * vs - v * C) ^ 2 / (A * v) ≤
      2 * A * W + 8 * (v / A) * M ^ 2 := by
    calc
      _ ≤ (2 * (A * vs) ^ 2 + 2 * (v * (As - C)) ^ 2) / (A * v) :=
        div_le_div_of_nonneg_right hsum (mul_pos hA hv).le
      _ = 2 * A * (vs ^ 2 / v) + 2 * (v / A) * (As - C) ^ 2 := by
        field_simp [hA.ne', hv.ne']
      _ ≤ 2 * A * W + 2 * (v / A) * (4 * M ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hvsdiv (by positivity))
          (mul_le_mul_of_nonneg_left hb2 (by positivity))
      _ = 2 * A * W + 8 * (v / A) * M ^ 2 := by ring
  have hva : v / A ≤ d ^ 5 / c := by
    apply (div_le_iff₀ hA).2
    calc
      v ≤ d ^ 6 := hvd
      _ = (d ^ 5 / c) * (c * d) := by field_simp [hc.ne']
      _ ≤ (d ^ 5 / c) * A := mul_le_mul_of_nonneg_left hAlo (by positivity)
  have hvsD : v / A ≤ D ^ 5 / c := hva.trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hd.le hdD 5) hc.le)
  have hvD : v ≤ D ^ 6 := hvd.trans (pow_le_pow_left₀ hd.le hdD 6)
  have hWD : W ≤ Cv ^ 2 * (D ^ 2 + D ^ 3) ^ 2 := by
    dsimp [W]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg Cv)
    apply pow_le_pow_left₀ (by positivity : 0 ≤ d ^ 2 + d ^ 3)
    exact add_le_add (pow_le_pow_left₀ hd.le hdD 2) (pow_le_pow_left₀ hd.le hdD 3)
  have hAW : 2 * A * W ≤ 2 * M * W := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hAM (by norm_num)) hW
  calc
    _ ≤ (2 * W + 2 * v * M ^ 2) + (2 * A * W + 8 * (v / A) * M ^ 2) :=
      add_le_add ht hsraw
    _ ≤ 2 * (1 + M) * W + 2 * v * M ^ 2 + 8 * (v / A) * M ^ 2 := by
      nlinarith only [hAW]
    _ ≤ 2 * (1 + M) * (Cv ^ 2 * (D ^ 2 + D ^ 3) ^ 2) +
        2 * D ^ 6 * M ^ 2 + 8 * (D ^ 5 / c) * M ^ 2 := by
      apply add_le_add
      · exact add_le_add
          (mul_le_mul_of_nonneg_left hWD (by positivity))
          (by nlinarith only [mul_le_mul_of_nonneg_right hvD (sq_nonneg M)])
      · nlinarith only [mul_le_mul_of_nonneg_right hvsD (sq_nonneg M)]
    _ = ellipticRatioConstant D c Cv M := by unfold ellipticRatioConstant; ring

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticGradient
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

def coordinateSubsetIntegral (S : Set Coord) (f : Coord → ℝ) : ℝ :=
  ∫ q in (fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' S, f (boxPoint q.1 q.2)

variable {tl tr sb st : ℝ} {S : Set Coord} {F G : Coord → ℝ}

theorem coordinateRectangle_closed_area_integrable
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    IntegrableOn (fun q : ℝ × ℝ => F (boxPoint q.1 q.2)) (Icc tl tr ×ˢ Icc sb st) := by
  have hc : ContinuousOn (fun q : ℝ × ℝ => F (boxPoint q.1 q.2))
      (Icc tl tr ×ˢ Icc sb st) :=
    hF.comp (by unfold boxPoint; fun_prop) (fun q hq => boxPoint_mem hq.1 hq.2)
  exact hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem rectangleIntegral_eq_closed_area (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st F =
      ∫ q in Icc tl tr ×ˢ Icc sb st, F (boxPoint q.1 q.2) := by
  rw [rectangleIntegral_swap ht hs hF]
  simp_rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le hs,
    ← integral_Icc_eq_integral_Ioc]
  have hi : IntegrableOn (fun q : ℝ × ℝ => F (boxPoint q.1 q.2))
      (Icc tl tr ×ˢ Icc sb st) (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod] using coordinateRectangle_closed_area_integrable hF
  simpa only [← Measure.volume_eq_prod] using
    (setIntegral_prod (fun q : ℝ × ℝ => F (boxPoint q.1 q.2)) hi).symm

theorem coordinateSubset_preimage_mem (hSbox : S ⊆ closedRectangle tl tr sb st)
    {q : ℝ × ℝ} (hq : q ∈ (fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' S) :
    q ∈ Icc tl tr ×ˢ Icc sb st := by
  have hp := hSbox hq
  change q.1 ∈ Icc tl tr ∧ q.2 ∈ Icc sb st
  change (boxPoint q.1 q.2) 0 ∈ Icc tl tr ∧ (boxPoint q.1 q.2) 1 ∈ Icc sb st at hp
  have h0 : (boxPoint q.1 q.2) 0 = q.1 := by simp [boxPoint]
  have h1 : (boxPoint q.1 q.2) 1 = q.2 := by simp [boxPoint]
  rwa [h0, h1] at hp

theorem coordinateSubset_integrable
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hSbox : S ⊆ closedRectangle tl tr sb st) :
    IntegrableOn (fun q : ℝ × ℝ => F (boxPoint q.1 q.2))
      ((fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' S) :=
  (coordinateRectangle_closed_area_integrable hF).mono_set
    (fun _ hq => coordinateSubset_preimage_mem hSbox hq)

theorem coordinateSubsetIntegral_mono (hS : MeasurableSet S)
    (hSbox : S ⊆ closedRectangle tl tr sb st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hG : ContinuousOn G (closedRectangle tl tr sb st))
    (hle : ∀ p ∈ S, F p ≤ G p) :
    coordinateSubsetIntegral S F ≤ coordinateSubsetIntegral S G := by
  have hm : MeasurableSet ((fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' S) :=
    hS.preimage (by unfold boxPoint; fun_prop)
  apply setIntegral_mono_on (coordinateSubset_integrable hF hSbox)
    (coordinateSubset_integrable hG hSbox) hm
  intro q hq
  exact hle (boxPoint q.1 q.2) hq

theorem coordinateSubsetIntegral_le_rectangle
    (ht : tl ≤ tr) (hs : sb ≤ st) (hSbox : S ⊆ closedRectangle tl tr sb st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hn : ∀ p ∈ closedRectangle tl tr sb st, 0 ≤ F p) :
    coordinateSubsetIntegral S F ≤ rectangleIntegral tl tr sb st F := by
  rw [rectangleIntegral_eq_closed_area ht hs hF]
  have hnonneg : (0 : ℝ × ℝ → ℝ) ≤ᵐ[volume.restrict (Icc tl tr ×ˢ Icc sb st)]
      (fun q => F (boxPoint q.1 q.2)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with q hq
    exact hn (boxPoint q.1 q.2) (boxPoint_mem hq.1 hq.2)
  exact setIntegral_mono_set (coordinateRectangle_closed_area_integrable hF) hnonneg
    (Filter.Eventually.of_forall (fun _ hq => coordinateSubset_preimage_mem hSbox hq))

theorem coordinateSubsetIntegral_const_mul (S : Set Coord) (r : ℝ) (F : Coord → ℝ) :
    coordinateSubsetIntegral S (fun p => r * F p) = r * coordinateSubsetIntegral S F := by
  unfold coordinateSubsetIntegral
  exact integral_const_mul r _

theorem restricted_gradient_from_energy
    (ht : tl ≤ tr) (hs : sb ≤ st) (hS : MeasurableSet S)
    (hSbox : S ⊆ closedRectangle tl tr sb st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hG : ContinuousOn G (closedRectangle tl tr sb st))
    (hn : ∀ p ∈ closedRectangle tl tr sb st, 0 ≤ G p)
    {Q : ℝ} (hQ : 0 ≤ Q) (hFG : ∀ p ∈ S, F p ≤ Q * G p) :
    coordinateSubsetIntegral S F ≤ Q * rectangleIntegral tl tr sb st G := by
  calc
    _ ≤ coordinateSubsetIntegral S (fun p => Q * G p) :=
      coordinateSubsetIntegral_mono hS hSbox hF (continuousOn_const.mul hG) hFG
    _ = Q * coordinateSubsetIntegral S G := coordinateSubsetIntegral_const_mul _ _ _
    _ ≤ Q * rectangleIntegral tl tr sb st G :=
      mul_le_mul_of_nonneg_left (coordinateSubsetIntegral_le_rectangle ht hs hSbox hG hn) hQ

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapAreaFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Sobolev

theorem rectangleIntegral_eq_coordinate_closed_area
    {tl tr sb st : ℝ} {F : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st F = ∫ p in closedRectangle tl tr sb st, F p := by
  rw [rectangleIntegral_eq_closed_area ht hs hF]
  have hh := (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.finTwoArrow (α := ℝ)).measurableEmbedding
    (fun q : ℝ × ℝ => F (boxPoint q.1 q.2)) (Icc tl tr ×ˢ Icc sb st)
  change (∫ p in closedRectangle tl tr sb st, F (boxPoint (p 0) (p 1))) =
    ∫ q in Icc tl tr ×ˢ Icc sb st, F (boxPoint q.1 q.2) at hh
  simpa only [boxPoint_eta] using hh.symm

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapFlowUniqueness
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem cap_trajectory_mem_ball_of_displacement {Y : ℝ → ℝ → ℝ}
    (hdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50)
    {s t : ℝ} (hs : s ∈ Ioo (-2:ℝ) 2) (ht : t ∈ Ioo (-2:ℝ) 2) :
    Y s t ∈ closedBall (0:ℝ) 3 := by
  have hp : coordinatePoint t s ∈ capChartDomain := by
    change coordinatePoint t s 0 ∈ Ioo (-2:ℝ) 2 ∧ coordinatePoint t s 1 ∈ Ioo (-2:ℝ) 2
    simpa [coordinatePoint] using (show t ∈ Ioo (-2:ℝ) 2 ∧ s ∈ Ioo (-2:ℝ) 2 from ⟨ht,hs⟩)
  have hd : |Y s t-s| ≤ (1:ℝ)/50 := by
    simpa [capFlowHeight,coordinatePoint] using hdisp (coordinatePoint t s) hp
  have hy : |Y s t| ≤ 3 := by
    have hh : |Y s t| ≤ |Y s t-s|+|s| := by
      simpa only [sub_add_cancel] using abs_add_le (Y s t-s) s
    have hs' : |s| < 2 := abs_lt.mpr hs
    linarith
  simpa only [mem_closedBall,Real.dist_eq,sub_zero] using hy

end SmoothLocal.Flow

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

def coordinateGradientSquare (f : Coord → ℝ) (p : Coord) : ℝ :=
  (coordPartial 0 f p)^2+(coordPartial 1 f p)^2

theorem coordinateGradientSquare_nonneg (f : Coord → ℝ) (p : Coord) :
    0 ≤ coordinateGradientSquare f p := add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem coordinateGradientSquare_contDiffOn {f : Coord → ℝ} {V : Set Coord}
    (hf : ContDiffOn ℝ ∞ f V) (hV : IsOpen V) :
    ContDiffOn ℝ ∞ (coordinateGradientSquare f) V :=
  ((partial_contDiffOn hf hV 0).pow 2).add ((partial_contDiffOn hf hV 1).pow 2)

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapInteriorEnergy
attribute [-instance] _root_.OAI.SmoothLocal.Geometry.instCountablePatchAddress
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry SmoothLocal.Flow

theorem capInteriorWeightFloor_pos {top b lambda MI : ℝ} (htop : top < b) :
    0 < capInteriorWeightFloor top b lambda MI :=
  mul_pos (pow_pos (sub_pos.mpr htop) _) (Real.exp_pos _)

theorem directedWeight_interior_lower {I : Coord → ℝ} {p : Coord} {top b lambda MI : ℝ}
    (htop : top < b) (hlambda : 0 ≤ lambda) (hp : p 1 ≤ top) (hI : |I p| ≤ MI) :
    capInteriorWeightFloor top b lambda MI ≤ directedWeight b lambda I p := by
  have hdist : b-top ≤ edgeDistance b p := by unfold edgeDistance; linarith
  have hpow := pow_le_pow_left₀ (sub_pos.mpr htop).le hdist 8
  have hphase : -lambda*top-MI ≤ weightPhase lambda I p := by
    have hm := mul_le_mul_of_nonneg_left hp hlambda
    unfold weightPhase
    linarith [(abs_le.mp hI).1]
  exact mul_le_mul hpow (Real.exp_le_exp.mpr hphase) (Real.exp_pos _).le
    (pow_nonneg ((sub_pos.mpr htop).le.trans hdist) _)

theorem closedRectangle_measurable (tl tr sb st : ℝ) : MeasurableSet (closedRectangle tl tr sb st) := by
  have h0 : IsClosed ((fun p : Coord => p 0) ⁻¹' Icc tl tr) := isClosed_Icc.preimage (continuous_apply 0)
  have h1 : IsClosed ((fun p : Coord => p 1) ⁻¹' Icc sb st) := isClosed_Icc.preimage (continuous_apply 1)
  exact (h0.inter h1).measurableSet

theorem coordinateSubsetIntegral_closedRectangle (tl tr sb st : ℝ) (F : Coord → ℝ)
    (ht : tl ≤ tr) (hs : sb ≤ st) (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    coordinateSubsetIntegral (closedRectangle tl tr sb st) F = rectangleIntegral tl tr sb st F := by
  rw [rectangleIntegral_eq_closed_area ht hs hF]
  have hpre : (fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' closedRectangle tl tr sb st =
      Icc tl tr ×ˢ Icc sb st := by
    ext q
    simp [closedRectangle,boxPoint,Prod.le_def,and_left_comm,and_assoc]
  unfold coordinateSubsetIntegral
  rw [hpre]

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedFarNegative
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem directedPrincipal_abs_bound {A : Coord → ℝ} {p : Coord}
    (ell : ℕ) {epsilon R MAs MAt : ℝ} (heps : 0 ≤ epsilon)
    (ht : |p 0| ≤ R) (hAs : |coordPartial 1 A p| ≤ MAs)
    (hAt : |coordPartial 0 A p| ≤ MAt) :
    |directedPrincipal A ell epsilon p| ≤ directedPrincipalBound ell epsilon R MAs MAt := by
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have hMAt : 0 ≤ MAt := (abs_nonneg _).trans hAt
  have hbeta : 0 ≤ (ell : ℝ) + 1 / 2 := by positivity
  have hfirst : |-((ell : ℝ) + 1 / 2) * coordPartial 1 A p| ≤ ((ell : ℝ) + 1 / 2) * MAs := by
    rw [abs_mul, abs_neg, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left hAs hbeta
  have hsecond : |epsilon * p 0 * coordPartial 0 A p / 2| ≤ epsilon * R * MAt / 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg heps, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left ht heps) hAt (abs_nonneg _) (mul_nonneg heps hR))
      (by norm_num)
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_WeightPrimitiveParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Flow

variable {B : Coord → ℝ} {R a b : ℝ}

theorem coefficient_pair_contDiffOn
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => B (coordinatePoint p.1 p.2)) (pairRectangle R a b) := by
  have hpoint : ContDiff ℝ ∞ (fun p : ℝ × ℝ => coordinatePoint p.1 p.2) := by
    unfold coordinatePoint
    fun_prop
  exact hB.comp hpoint.contDiffOn (fun p hp => point_mem_rectangle hp.1 hp.2)

theorem coordinatePrimitive_segment_intervalIntegrable
    (hB : ContinuousOn B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b) :
    IntervalIntegrable (fun t => B (coordinatePoint t (p 1))) volume 0 (p 0) := by
  have hc : ContinuousOn (fun t => B (coordinatePoint t (p 1))) (Ioo (-R) R) :=
    hB.comp (by unfold coordinatePoint; fun_prop)
      (fun t ht => point_mem_rectangle ht hp.2)
  have hz : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
  have hseg : uIcc 0 (p 0) ⊆ Ioo (-R) R := by
    intro t ht
    exact ⟨lt_of_lt_of_le (lt_min hz.1 hp.1.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hz.2 hp.1.2)⟩
  exact (hc.mono hseg).intervalIntegrable

theorem coordinatePrimitive_abs_bound
    (hB : ContinuousOn B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b)
    {M : ℝ} (hbound : ∀ q ∈ coordinateRectangle R a b, |B q| ≤ M) :
    |coordinatePrimitive B p| ≤ R * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbound p hp)
  have hz : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
  have hseg : uIcc 0 (p 0) ⊆ Ioo (-R) R := by
    intro t ht
    exact ⟨lt_of_lt_of_le (lt_min hz.1 hp.1.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hz.2 hp.1.2)⟩
  have hi := coordinatePrimitive_segment_intervalIntegrable hB hR hp
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := p 0) (C := M)
    (f := fun t => B (coordinatePoint t (p 1)))
    (fun t ht => by
      rw [Real.norm_eq_abs]
      exact hbound _ (point_mem_rectangle (hseg (uIoc_subset_uIcc ht)) hp.2))
  calc
    _ ≤ M * |p 0| := by simpa only [coordinatePrimitive, Real.norm_eq_abs, sub_zero] using hb
    _ ≤ M * R := mul_le_mul_of_nonneg_left (abs_lt.mpr hp.1).le hM
    _ = R * M := mul_comm _ _

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowSecondVariation
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem flowPullback_contDiffOn {C : Coord → ℝ} (hC : ContDiffOn ℝ ∞ C U) :
    ContDiffOn ℝ ∞ (fun p => C (flowCoordinateMap Y p)) (pairRectangle 2 (-2) 2) := by
  have hF := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hT : ContDiffOn ℝ ∞ (flowCoordinateMap Y) (pairRectangle 2 (-2) 2) :=
    (contDiffOn_fst.smul contDiffOn_const).add (hF.smul contDiffOn_const)
  exact hC.comp hT (fun p hp => hSU
    (flowCoordinateMap_mem_modelSquare hq hU hSU hY hrange hstart hode hp))

theorem initialFlowDerivative_eq_pairPartialY {p : ℝ × ℝ}
    (hp : p ∈ pairRectangle 2 (-2) 2) :
    initialFlowDerivative Y p = pairPartialY (fun v : ℝ × ℝ => Y v.2 v.1) p := by
  have hF := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hd := ((hF.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  exact (hd.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

theorem initialFlowDerivative_contDiffOn :
    ContDiffOn ℝ ∞ (initialFlowDerivative Y) (pairRectangle 2 (-2) 2) := by
  have hF := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hd : ContDiffOn ℝ ∞ (pairPartialY (fun v : ℝ × ℝ => Y v.2 v.1))
      (pairRectangle 2 (-2) 2) :=
    (hF.fderiv_of_isOpen (pairRectangle_isOpen 2 (-2) 2) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const
  exact hd.congr (fun p hp => initialFlowDerivative_eq_pairPartialY
    hq hU hSU hY hrange hstart hode hp)

theorem flowPullback_partial_y {C : Coord → ℝ} (hC : ContDiffOn ℝ ∞ C U)
    {p : ℝ × ℝ} (hp : p ∈ pairRectangle 2 (-2) 2) :
    pairPartialY (fun v => C (flowCoordinateMap Y v)) p =
      coordPartial 1 C (flowCoordinateMap Y p) * initialFlowDerivative Y p := by
  have hsY : HasDerivAt (fun s => Y s p.1) (initialFlowDerivative Y p) p.2 :=
    (cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hp.2 hp.1).differentiableAt.hasDerivAt
  have hsT : HasDerivAt (fun s => flowCoordinateMap Y (p.1, s))
      (initialFlowDerivative Y p • Pi.single 1 (1 : ℝ)) p.2 := by
    convert
      ((hasDerivAt_const p.2 p.1).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add
        (hsY.smul_const (Pi.single 1 (1 : ℝ) : Coord)) using 1 <;>
      first | rfl | simp
  have hmem := hSU (flowCoordinateMap_mem_modelSquare hq hU hSU hY hrange hstart hode hp)
  have hdC := ((hC.contDiffAt (hU.mem_nhds hmem)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hchain : HasDerivAt (fun s => C (flowCoordinateMap Y (p.1, s)))
      (coordPartial 1 C (flowCoordinateMap Y p) * initialFlowDerivative Y p) p.2 := by
    convert hdC.comp_hasDerivAt p.2 hsT using 1 <;>
      first | rfl | simp only [map_smul, smul_eq_mul, coordPartial, mul_comm]
  have hB := flowPullback_contDiffOn hq hU hSU hY hrange hstart hode hC
  have hdB : HasFDerivAt (fun v : ℝ × ℝ => C (flowCoordinateMap Y v))
      (fderiv ℝ (fun v : ℝ × ℝ => C (flowCoordinateMap Y v)) p) p :=
    ((hB.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hpair : HasDerivAt (fun s => C (flowCoordinateMap Y (p.1, s)))
      (pairPartialY (fun v => C (flowCoordinateMap Y v)) p) p.2 := by
    convert hdB.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)) using 1 <;> rfl
  exact hpair.unique hchain

theorem cap_flow_initial_second_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => deriv (fun v => Y v t) u)
      (-deriv (fun v => Y v t) s *
        (∫ r in 0..t, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
          deriv (fun v => Y v r) s)) s := by
  let B (p : ℝ × ℝ) := coordPartial 1 q (flowCoordinateMap Y p)
  have hB : ContDiffOn ℝ ∞ B (pairRectangle 2 (-2) 2) :=
    flowPullback_contDiffOn hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 1)
  have hI := pairPrimitive_hasDerivAt_y (hB.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) ht hs
  have hdiag : pairPrimitive (pairPartialY B) (t, s) =
      ∫ r in 0..t, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
        deriv (fun v => Y v r) s := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Ioo (-2 : ℝ) 2 := by
      have hz : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := by norm_num
      exact ⟨(lt_min hz.1 ht.1).trans_le hr.1, hr.2.trans_lt (max_lt hz.2 ht.2)⟩
    exact flowPullback_partial_y hq hU hSU hY hrange hstart hode
      (partial_contDiffOn hq hU 1) ⟨hr', hs⟩
  have hV : HasDerivAt (fun u => Real.exp (-pairPrimitive B (t, u)))
      (Real.exp (-pairPrimitive B (t, s)) * -pairPrimitive (pairPartialY B) (t, s)) s := hI.neg.exp
  have he : (fun u => deriv (fun v => Y v t) u) =ᶠ[𝓝 s]
      (fun u => Real.exp (-pairPrimitive B (t, u))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact (cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hu ht).deriv
  have hVs : Real.exp (-pairPrimitive B (t, s)) = deriv (fun v => Y v t) s :=
    (cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hs ht).deriv.symm
  rw [hdiag, hVs] at hV
  convert hV.congr_of_eventuallyEq he using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

theorem cap_flow_initial_second_formula {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    deriv (fun u => deriv (fun v => Y v t) u) s =
      -deriv (fun v => Y v t) s *
        (∫ r in 0..t, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
          deriv (fun v => Y v r) s) :=
  (cap_flow_initial_second_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

theorem flow_initial_second_integral_bound {M : ℝ} (hM : 0 ≤ M)
    (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hMqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    IntervalIntegrable (fun r => coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
      deriv (fun v => Y v r) s) volume 0 t ∧
    |∫ r in 0..t, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
      deriv (fun v => Y v r) s| ≤ 2 * M * Real.exp (2 * M) := by
  let C (p : ℝ × ℝ) := coordPartial 1 (coordPartial 1 q) (flowCoordinateMap Y p) * initialFlowDerivative Y p
  have hC : ContDiffOn ℝ ∞ C (pairRectangle 2 (-2) 2) :=
    (flowPullback_contDiffOn hq hU hSU hY hrange hstart hode
      (partial_contDiffOn (partial_contDiffOn hq hU 1) hU 1)).mul
      (initialFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode)
  have hc : ContinuousOn (fun r => C (r, s)) (Ioo (-2 : ℝ) 2) :=
    hC.continuousOn.comp (f := fun r => (r, s)) (by fun_prop) (fun r hr => ⟨hr, hs⟩)
  have hseg : uIcc (0 : ℝ) t ⊆ Ioo (-2 : ℝ) 2 := by
    intro r hr
    have hz : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := by norm_num
    exact ⟨(lt_min hz.1 ht.1).trans_le hr.1, hr.2.trans_lt (max_lt hz.2 ht.2)⟩
  refine ⟨(hc.mono hseg).intervalIntegrable, ?_⟩
  have hbound (r : ℝ) (hr : r ∈ uIcc (0 : ℝ) t) :
      ‖coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) * deriv (fun v => Y v r) s‖ ≤
        M * Real.exp (2 * M) := by
    have hr' := hseg hr
    have hys := cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hs hr'
    have hpos := cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs hr'
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
    exact mul_le_mul (hMqq _ (flowCoordinateMap_mem_modelSquare (p := (r, s)) hq hU hSU hY hrange hstart hode
      ⟨hr', hs⟩)) hys.2 hpos.le hM
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (C := M * Real.exp (2 * M))
    (fun r hr => hbound r (uIoc_subset_uIcc hr))
  have ht2 : |t| ≤ 2 := (abs_lt.mpr ht).le
  calc
    _ ≤ (M * Real.exp (2 * M)) * |t| := by simpa only [Real.norm_eq_abs, sub_zero] using hi
    _ ≤ (M * Real.exp (2 * M)) * 2 := mul_le_mul_of_nonneg_left ht2
      (mul_nonneg hM (Real.exp_pos _).le)
    _ = 2 * M * Real.exp (2 * M) := by ring

theorem cap_flow_initial_second_bound {M : ℝ} (hM : 0 ≤ M)
    (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hMqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => deriv (fun v => Y v t) u) s| ≤ 2 * M * Real.exp (4 * M) := by
  rw [cap_flow_initial_second_formula hq hU hSU hY hrange hstart hode hs ht, abs_mul,
    abs_neg, abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht)]
  calc
    _ ≤ Real.exp (2 * M) * (2 * M * Real.exp (2 * M)) :=
      mul_le_mul (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hs ht).2
        (flow_initial_second_integral_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hs ht).2
        (abs_nonneg _) (Real.exp_pos _).le
    _ = (2 * M) * (Real.exp (2 * M) * Real.exp (2 * M)) := by ring
    _ = 2 * M * Real.exp (4 * M) := by
      rw [← Real.exp_add]
      congr 2
      ring

end ActualFlow
end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowThirdVariation
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

def initialSecondForcing (q : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ r in 0..p.1, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y p.2 r)) *
    deriv (fun v => Y v r) p.2

def initialThirdForcing (q : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ r in 0..p.1,
    coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (coordinatePoint r (Y p.2 r)) *
      (deriv (fun v => Y v r) p.2) ^ 2 +
    coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y p.2 r)) *
      deriv (fun u => deriv (fun v => Y v r) u) p.2

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem flowPullback_hasDerivAt_y {C : Coord → ℝ} (hC : ContDiffOn ℝ ∞ C U)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => C (coordinatePoint t (Y u t)))
      (coordPartial 1 C (coordinatePoint t (Y s t)) * deriv (fun u => Y u t) s) s := by
  have hB := flowPullback_contDiffOn hq hU hSU hY hrange hstart hode hC
  have hd : HasFDerivAt (fun p : ℝ × ℝ => C (flowCoordinateMap Y p))
      (fderiv ℝ (fun p : ℝ × ℝ => C (flowCoordinateMap Y p)) (t, s)) (t, s) :=
    ((hB.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds ⟨ht, hs⟩)).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hh := hd.comp_hasDerivAt s ((hasDerivAt_const s t).prodMk (hasDerivAt_id s))
  change HasDerivAt (fun u => C (coordinatePoint t (Y u t)))
    (pairPartialY (fun p => C (flowCoordinateMap Y p)) (t, s)) s at hh
  rw [flowPullback_partial_y hq hU hSU hY hrange hstart hode hC ⟨ht, hs⟩] at hh
  exact hh

theorem initialSecondFlowDerivative_contDiffOn :
    ContDiffOn ℝ ∞ (initialSecondFlowDerivative Y) (pairRectangle 2 (-2) 2) := by
  have hV := initialFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode
  have hd : ContDiffOn ℝ ∞ (pairPartialY (initialFlowDerivative Y))
      (pairRectangle 2 (-2) 2) :=
    (hV.fderiv_of_isOpen (pairRectangle_isOpen 2 (-2) 2) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const
  apply hd.congr
  intro p hp
  have hder := ((hV.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  exact (hder.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

theorem initialSecondForcing_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => initialSecondForcing q Y (t, u))
      (initialThirdForcing q Y (t, s)) s := by
  let C (p : ℝ × ℝ) := coordPartial 1 (coordPartial 1 q) (flowCoordinateMap Y p) *
    initialFlowDerivative Y p
  have hqq := partial_contDiffOn (partial_contDiffOn hq hU 1) hU 1
  have hC : ContDiffOn ℝ ∞ C (pairRectangle 2 (-2) 2) :=
    (flowPullback_contDiffOn hq hU hSU hY hrange hstart hode hqq).mul
      (initialFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode)
  have hi := pairPrimitive_hasDerivAt_y (hC.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) ht hs
  have heq : pairPrimitive (pairPartialY C) (t, s) = initialThirdForcing q Y (t, s) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hz : (0 : ℝ) ∈ Ioo (-2) 2 := by norm_num
    have hr' : r ∈ Ioo (-2 : ℝ) 2 :=
      ⟨(lt_min hz.1 ht.1).trans_le hr.1, hr.2.trans_lt (max_lt hz.2 ht.2)⟩
    have hqder := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode hqq hs hr'
    have hVder := (cap_flow_initial_second_hasDerivAt hq hU hSU hY hrange hstart hode hs hr').differentiableAt.hasDerivAt
    have hprod := hqder.mul hVder
    have hfd : HasFDerivAt C (fderiv ℝ C (r, s)) (r, s) :=
      ((hC.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds ⟨hr', hs⟩)).differentiableAt
        (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
    have he := (hfd.comp_hasDerivAt s
      ((hasDerivAt_const s r).prodMk (hasDerivAt_id s))).unique hprod
    change pairPartialY C (r, s) = _ at he
    change pairPartialY C (r, s) = _
    rw [he]
    ring
  rw [heq] at hi
  exact hi

theorem cap_flow_initial_third_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => initialSecondFlowDerivative Y (t, u))
      (-initialSecondFlowDerivative Y (t, s) * initialSecondForcing q Y (t, s) -
        initialFlowDerivative Y (t, s) * initialThirdForcing q Y (t, s)) s := by
  have hV : HasDerivAt (fun u => initialFlowDerivative Y (t, u))
      (initialSecondFlowDerivative Y (t, s)) s :=
    (cap_flow_initial_second_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).differentiableAt.hasDerivAt
  have hI := initialSecondForcing_hasDerivAt hq hU hSU hY hrange hstart hode hs ht
  have hproduct : HasDerivAt
      (fun u => -initialFlowDerivative Y (t, u) * initialSecondForcing q Y (t, u))
      (-initialSecondFlowDerivative Y (t, s) * initialSecondForcing q Y (t, s) +
        -initialFlowDerivative Y (t, s) * initialThirdForcing q Y (t, s)) s := hV.neg.mul hI
  have he : (fun u => initialSecondFlowDerivative Y (t, u)) =ᶠ[𝓝 s]
      (fun u => -initialFlowDerivative Y (t, u) * initialSecondForcing q Y (t, u)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact cap_flow_initial_second_formula hq hU hSU hY hrange hstart hode hu ht
  convert hproduct.congr_of_eventuallyEq he using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

theorem cap_flow_initial_third_formula {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    deriv (fun u => initialSecondFlowDerivative Y (t, u)) s =
      -initialSecondFlowDerivative Y (t, s) * initialSecondForcing q Y (t, s) -
        initialFlowDerivative Y (t, s) * initialThirdForcing q Y (t, s) :=
  (cap_flow_initial_third_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

theorem initialThirdForcing_integrable_bound {M : ℝ} (hM : 0 ≤ M)
    (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hMqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 q) p| ≤ M)
    (hMqqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 (coordPartial 1 q)) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    IntervalIntegrable (fun r =>
      coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (coordinatePoint r (Y s r)) *
        (deriv (fun v => Y v r) s)^2 +
      coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
        deriv (fun u => deriv (fun v => Y v r) u) s) volume 0 t ∧
    |initialThirdForcing q Y (t, s)| ≤ (2 * M + 4 * M^2) * Real.exp (4 * M) := by
  let C (p : ℝ × ℝ) :=
    coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (flowCoordinateMap Y p) * (initialFlowDerivative Y p)^2 +
    coordPartial 1 (coordPartial 1 q) (flowCoordinateMap Y p) * initialSecondFlowDerivative Y p
  have hqq := partial_contDiffOn (partial_contDiffOn hq hU 1) hU 1
  have hC : ContDiffOn ℝ ∞ C (pairRectangle 2 (-2) 2) :=
    ((flowPullback_contDiffOn hq hU hSU hY hrange hstart hode (partial_contDiffOn hqq hU 1)).mul
      ((initialFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode).pow 2)).add
      ((flowPullback_contDiffOn hq hU hSU hY hrange hstart hode hqq).mul
        (initialSecondFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode))
  have hc : ContinuousOn (fun r => C (r, s)) (Ioo (-2 : ℝ) 2) :=
    hC.continuousOn.comp (f := fun r => (r, s)) (by fun_prop) (fun r hr => ⟨hr, hs⟩)
  have hseg : uIcc (0 : ℝ) t ⊆ Ioo (-2 : ℝ) 2 := by
    intro r hr
    have hz : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := by norm_num
    exact ⟨(lt_min hz.1 ht.1).trans_le hr.1, hr.2.trans_lt (max_lt hz.2 ht.2)⟩
  refine ⟨(hc.mono hseg).intervalIntegrable, ?_⟩
  have hbound (r : ℝ) (hr : r ∈ uIcc (0 : ℝ) t) :
      ‖C (r, s)‖ ≤ (M + 2 * M^2) * Real.exp (4 * M) := by
    have hr' := hseg hr
    have hp := flowCoordinateMap_mem_modelSquare (p := (r, s)) hq hU hSU hY hrange hstart hode ⟨hr', hs⟩
    have hV := (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hs hr').2
    have hVpos := cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs hr'
    have hVsq : |(deriv (fun v => Y v r) s)^2| ≤ Real.exp (4 * M) := by
      rw [abs_of_nonneg (sq_nonneg _)]
      calc
        _ ≤ (Real.exp (2 * M))^2 := pow_le_pow_left₀ hVpos.le hV 2
        _ = Real.exp (4 * M) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
    have hW := cap_flow_initial_second_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hs hr'
    rw [Real.norm_eq_abs]
    calc
      |C (r, s)| ≤
          |coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (coordinatePoint r (Y s r))| *
            |(deriv (fun v => Y v r) s)^2| +
          |coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r))| *
            |deriv (fun u => deriv (fun v => Y v r) u) s| := by
        calc
          _ ≤ |coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (coordinatePoint r (Y s r)) *
              (deriv (fun v => Y v r) s)^2| +
              |coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
                deriv (fun u => deriv (fun v => Y v r) u) s| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ M * Real.exp (4 * M) + M * (2 * M * Real.exp (4 * M)) :=
        add_le_add (mul_le_mul (hMqqq _ hp) hVsq (abs_nonneg _) hM)
          (mul_le_mul (hMqq _ hp) hW (abs_nonneg _) hM)
      _ = (M + 2 * M^2) * Real.exp (4 * M) := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (C := (M + 2 * M^2) * Real.exp (4 * M)) (f := fun r => C (r, s))
    (fun r hr => hbound r (uIoc_subset_uIcc hr))
  have ht2 : |t| ≤ 2 := (abs_lt.mpr ht).le
  calc
    _ ≤ ((M + 2 * M^2) * Real.exp (4 * M)) * |t| := by
      simpa only [Real.norm_eq_abs, sub_zero, initialThirdForcing, C,
        flowCoordinateMap, initialFlowDerivative, initialSecondFlowDerivative] using hi
    _ ≤ ((M + 2 * M^2) * Real.exp (4 * M)) * 2 := mul_le_mul_of_nonneg_left ht2
      (mul_nonneg (by positivity) (Real.exp_pos _).le)
    _ = (2 * M + 4 * M^2) * Real.exp (4 * M) := by ring

theorem cap_flow_initial_third_bound {M : ℝ} (hM : 0 ≤ M)
    (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hMqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 q) p| ≤ M)
    (hMqqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 (coordPartial 1 q)) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => initialSecondFlowDerivative Y (t, u)) s| ≤
      (2 * M + 8 * M^2) * Real.exp (6 * M) := by
  rw [cap_flow_initial_third_formula hq hU hSU hY hrange hstart hode hs ht]
  have hW := cap_flow_initial_second_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hs ht
  have hI := (flow_initial_second_integral_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hs ht).2
  have hJ := (initialThirdForcing_integrable_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hMqqq hs ht).2
  have hV : |initialFlowDerivative Y (t, s)| ≤ Real.exp (2 * M) := by
    unfold initialFlowDerivative
    rw [abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht)]
    exact (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hs ht).2
  calc
    _ ≤ |initialSecondFlowDerivative Y (t, s)| * |initialSecondForcing q Y (t, s)| +
        |initialFlowDerivative Y (t, s)| * |initialThirdForcing q Y (t, s)| := by
      simpa only [abs_mul, abs_neg] using
        abs_sub (-(initialSecondFlowDerivative Y (t, s)) * initialSecondForcing q Y (t, s))
          (initialFlowDerivative Y (t, s) * initialThirdForcing q Y (t, s))
    _ ≤ (2 * M * Real.exp (4 * M)) * (2 * M * Real.exp (2 * M)) +
        Real.exp (2 * M) * ((2 * M + 4 * M^2) * Real.exp (4 * M)) :=
      add_le_add (mul_le_mul hW hI (abs_nonneg _) (by positivity))
        (mul_le_mul hV hJ (abs_nonneg _) (Real.exp_pos _).le)
    _ = (2 * M + 8 * M^2) * (Real.exp (2 * M) * Real.exp (4 * M)) := by ring
    _ = (2 * M + 8 * M^2) * Real.exp (6 * M) := by
      rw [← Real.exp_add]
      congr 2
      ring

end ActualFlow
end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowTimeVariation
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

def mixedFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun u => timeFlowDerivative Y (p.1, u)) p.2

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem flowPullback_hasDerivAt_t {C : Coord → ℝ} (hC : ContDiffOn ℝ ∞ C U)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => C (coordinatePoint u (Y s u)))
      (coordPartial 0 C (coordinatePoint t (Y s t)) -
        q (coordinatePoint t (Y s t)) * coordPartial 1 C (coordinatePoint t (Y s t))) t := by
  have hT : HasDerivAt (fun u => coordinatePoint u (Y s u))
      (Pi.single 0 (1 : ℝ) - q (coordinatePoint t (Y s t)) • Pi.single 1 (1 : ℝ) : Coord) t := by
    convert
      ((hasDerivAt_id t).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add
        ((cap_flow_time_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).smul_const
          (Pi.single 1 (1 : ℝ) : Coord)) using 1 <;>
      first | rfl | simp only [coordinatePoint, one_smul, neg_smul, sub_eq_add_neg]
  have hp := hSU (flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩)
  have hC' := ((hC.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  convert hC'.comp_hasDerivAt t hT using 1 <;>
    first | rfl | simp only [map_sub, map_smul, smul_eq_mul, coordPartial, flowCoordinateMap]

theorem cap_flow_mixed_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => timeFlowDerivative Y (t, u))
      (-coordPartial 1 q (coordinatePoint t (Y s t)) * initialFlowDerivative Y (t, s)) s := by
  have hd := (flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode hq hs ht).neg
  have he : (fun u => timeFlowDerivative Y (t, u)) =ᶠ[𝓝 s]
      (fun u => -q (coordinatePoint t (Y u t))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact timeFlowDerivative_eq hq hU hSU hY hrange hstart hode hu ht
  convert hd.congr_of_eventuallyEq he using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | (dsimp [initialFlowDerivative]; ring)

theorem mixedFlowDerivative_eq {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    mixedFlowDerivative Y (t, s) =
      -coordPartial 1 q (coordinatePoint t (Y s t)) * initialFlowDerivative Y (t, s) :=
  (cap_flow_mixed_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

theorem cap_flow_time_second_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => timeFlowDerivative Y (u, s))
      (-coordPartial 0 q (coordinatePoint t (Y s t)) +
        coordPartial 1 q (coordinatePoint t (Y s t)) * q (coordinatePoint t (Y s t))) t := by
  have hd := (flowPullback_hasDerivAt_t hq hU hSU hY hrange hstart hode hq hs ht).neg
  have he : (fun u => timeFlowDerivative Y (u, s)) =ᶠ[𝓝 t]
      (fun u => -q (coordinatePoint u (Y s u))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact timeFlowDerivative_eq hq hU hSU hY hrange hstart hode hs hu
  convert hd.congr_of_eventuallyEq he using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

theorem timeSecondFlowDerivative_eq {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    timeSecondFlowDerivative Y (t, s) =
      -coordPartial 0 q (coordinatePoint t (Y s t)) +
        coordPartial 1 q (coordinatePoint t (Y s t)) * q (coordinatePoint t (Y s t)) :=
  (cap_flow_time_second_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

theorem cap_flow_mixed_initial_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => mixedFlowDerivative Y (t, u))
      (-coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t)) *
          (initialFlowDerivative Y (t, s))^2 -
        coordPartial 1 q (coordinatePoint t (Y s t)) * initialSecondFlowDerivative Y (t, s)) s := by
  have hdq := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 1) hs ht
  have hdV : HasDerivAt (fun u => initialFlowDerivative Y (t, u))
      (initialSecondFlowDerivative Y (t, s)) s :=
    (cap_flow_initial_second_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).differentiableAt.hasDerivAt
  have hd := hdq.neg.mul hdV
  have he : (fun u => mixedFlowDerivative Y (t, u)) =ᶠ[𝓝 s]
      (fun u => -coordPartial 1 q (coordinatePoint t (Y u t)) * initialFlowDerivative Y (t, u)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact mixedFlowDerivative_eq hq hU hSU hY hrange hstart hode hu ht
  convert hd.congr_of_eventuallyEq he using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | (dsimp [initialFlowDerivative]; ring)

theorem cap_flow_time_second_initial_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => timeSecondFlowDerivative Y (t, u))
      ((-coordPartial 1 (coordPartial 0 q) (coordinatePoint t (Y s t)) +
        coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t)) * q (coordinatePoint t (Y s t)) +
        (coordPartial 1 q (coordinatePoint t (Y s t)))^2) * initialFlowDerivative Y (t, s)) s := by
  have hd0 := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 0) hs ht
  have hd1 := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 1) hs ht
  have hdq := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode hq hs ht
  have hd := hd0.neg.add (hd1.mul hdq)
  have he : (fun u => timeSecondFlowDerivative Y (t, u)) =ᶠ[𝓝 s]
      (fun u => -coordPartial 0 q (coordinatePoint t (Y u t)) +
        coordPartial 1 q (coordinatePoint t (Y u t)) * q (coordinatePoint t (Y u t))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact timeSecondFlowDerivative_eq hq hU hSU hY hrange hstart hode hu ht
  convert hd.congr_of_eventuallyEq he using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | (dsimp [initialFlowDerivative]; ring)

theorem cap_flow_time_third_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => timeSecondFlowDerivative Y (u, s))
      (-coordPartial 0 (coordPartial 0 q) (coordinatePoint t (Y s t)) +
        q (coordinatePoint t (Y s t)) * coordPartial 1 (coordPartial 0 q) (coordinatePoint t (Y s t)) +
        (coordPartial 0 (coordPartial 1 q) (coordinatePoint t (Y s t)) -
          q (coordinatePoint t (Y s t)) * coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t))) *
          q (coordinatePoint t (Y s t)) +
        coordPartial 1 q (coordinatePoint t (Y s t)) *
          (coordPartial 0 q (coordinatePoint t (Y s t)) -
            q (coordinatePoint t (Y s t)) * coordPartial 1 q (coordinatePoint t (Y s t)))) t := by
  have hd0 := flowPullback_hasDerivAt_t hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 0) hs ht
  have hd1 := flowPullback_hasDerivAt_t hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 1) hs ht
  have hdq := flowPullback_hasDerivAt_t hq hU hSU hY hrange hstart hode hq hs ht
  have hd := hd0.neg.add (hd1.mul hdq)
  have he : (fun u => timeSecondFlowDerivative Y (u, s)) =ᶠ[𝓝 t]
      (fun u => -coordPartial 0 q (coordinatePoint u (Y s u)) +
        coordPartial 1 q (coordinatePoint u (Y s u)) * q (coordinatePoint u (Y s u))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact timeSecondFlowDerivative_eq hq hU hSU hY hrange hstart hode hs hu
  convert hd.congr_of_eventuallyEq he using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

end ActualFlow
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

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem cap_flow_time_second_bound {M : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ 1)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |timeSecondFlowDerivative Y (t, s)| ≤ 2 * M := by
  rw [timeSecondFlowDerivative_eq hq hU hSU hY hrange hstart hode hs ht]
  have hp := flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩
  have hh := abs_transport_bound hM (hq1 0 _ hp) (hq1 1 _ hp) (hq0 _ hp)
  calc
    _ = |-(coordPartial 0 q (coordinatePoint t (Y s t)) -
        q (coordinatePoint t (Y s t)) * coordPartial 1 q (coordinatePoint t (Y s t)))| := by
      congr 1; ring
    _ = |coordPartial 0 q (coordinatePoint t (Y s t)) -
        q (coordinatePoint t (Y s t)) * coordPartial 1 q (coordinatePoint t (Y s t))| := abs_neg _
    _ ≤ 2 * M := hh

theorem cap_flow_mixed_bound {M : ℝ} (hM : 0 ≤ M)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |mixedFlowDerivative Y (t, s)| ≤ M * Real.exp (2 * M) := by
  rw [mixedFlowDerivative_eq hq hU hSU hY hrange hstart hode hs ht, abs_mul, abs_neg, initialFlowDerivative,
    abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht)]
  exact mul_le_mul (hq1 1 _
    (flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩))
    (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hs ht).2
    (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht).le hM

theorem cap_flow_mixed_initial_bound {M : ℝ} (hM : 0 ≤ M)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => mixedFlowDerivative Y (t, u)) s| ≤
      (M + 2 * M^2) * Real.exp (4 * M) := by
  rw [(cap_flow_mixed_initial_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv]
  have hp := flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩
  have hV := (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hs ht).2
  have hVpos := cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht
  have hVsq : |(initialFlowDerivative Y (t, s))^2| ≤ Real.exp (4 * M) := by
    rw [abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (Real.exp (2 * M))^2 := pow_le_pow_left₀ hVpos.le hV 2
      _ = Real.exp (4 * M) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hW := cap_flow_initial_second_bound hq hU hSU hY hrange hstart hode hM (hq1 1) (hq2 1 1) hs ht
  calc
    _ ≤ |coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t))| *
        |(initialFlowDerivative Y (t, s))^2| +
        |coordPartial 1 q (coordinatePoint t (Y s t))| * |initialSecondFlowDerivative Y (t, s)| := by
      calc
        _ ≤ |-coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t)) *
            (initialFlowDerivative Y (t, s))^2| +
            |coordPartial 1 q (coordinatePoint t (Y s t)) * initialSecondFlowDerivative Y (t, s)| :=
          abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_neg]
    _ ≤ M * Real.exp (4 * M) + M * (2 * M * Real.exp (4 * M)) :=
      add_le_add (mul_le_mul (hq2 1 1 _ hp) hVsq (abs_nonneg _) hM)
        (mul_le_mul (hq1 1 _ hp) hW (abs_nonneg _) hM)
    _ = (M + 2 * M^2) * Real.exp (4 * M) := by ring

theorem cap_flow_time_second_initial_bound {M : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ 1)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => timeSecondFlowDerivative Y (t, u)) s| ≤
      (2 * M + M^2) * Real.exp (2 * M) := by
  rw [(cap_flow_time_second_initial_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv,
    abs_mul, initialFlowDerivative, abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht)]
  have hp := flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩
  exact mul_le_mul
    (abs_second_initial_coefficient_bound hM (hq2 1 0 _ hp) (hq2 1 1 _ hp) (hq0 _ hp) (hq1 1 _ hp))
    (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hs ht).2
    (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht).le (by positivity)

theorem cap_flow_time_third_bound {M : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ 1)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => timeSecondFlowDerivative Y (u, s)) t| ≤ 4 * M + 2 * M^2 := by
  rw [(cap_flow_time_third_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv]
  have hp := flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩
  exact abs_third_time_coefficient_bound hM (hq0 _ hp)
    (hq2 0 0 _ hp) (hq2 1 0 _ hp) (hq2 0 1 _ hp) (hq2 1 1 _ hp)
    (hq1 0 _ hp) (hq1 1 _ hp)

end ActualFlow
end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_HeightEnergyJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

theorem darbouxG_lower_of_energy_floor
    (g : MetricField) (z : Coord → ℝ) (p : Coord) {e0 H : ℝ}
    (he0 : 0 < e0) (hE : e0 ≤ heightEnergy g z p) (hH : 0 ≤ H)
    (hupper : |covHessian g z p 1 1| ≤ H) (hne : covHessian g z p 1 1 ≠ 0) :
    e0 / (1 + H)^2 ≤ darbouxG g z p := by
  have hsq : (covHessian g z p 1 1)^2 ≤ (1 + H)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (covHessian g z p 1 1))
      (hupper.trans (by linarith : H ≤ 1 + H)) 2
    simpa only [sq_abs] using hh
  have hl : 0 ≤ e0 / (1 + H)^2 := by positivity
  have heq : e0 / (1 + H)^2 * (1 + H)^2 = e0 :=
    div_mul_cancel₀ _ (pow_ne_zero 2 (by linarith : (1 : ℝ) + H ≠ 0))
  unfold darbouxG
  apply (le_div_iff₀ (sq_pos_of_ne_zero hne)).mpr
  calc
    _ ≤ e0 / (1 + H)^2 * (1 + H)^2 := mul_le_mul_of_nonneg_left hsq hl
    _ = e0 := heq
    _ ≤ heightEnergy g z p := hE

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_HeightCoefficientClosedBounds
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.ODE

theorem curvatureDriftError_bound_original_data
    {g : MetricField} {z : Coord → ℝ} {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hEB : CoordinateBound (heightEnergy g z) modelSquare 3 (heightEnergyJetBound G Z))
    (hHB : CoordinateBound (fun p => covHessian g z p 1 1) modelSquare 3 (hessianJetBound G Z d))
    (hΓB : ∀ k i j : Fin 2, CoordinateBound (christoffel g k i j) modelSquare 3 (christoffelJetBound G d))
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ) / 100)
    {p : Coord} (hp : p ∈ modelSquare) :
    |curvatureDriftError g z p| ≤ heightDriftErrorBound G Z d c := by
  have ht : |connectionTraceY g p| ≤ 2 * christoffelJetBound G d := by
    exact ((abs_add_le _ _).trans
      (add_le_add (hΓB 0 0 1 [] (by norm_num) p hp) (hΓB 1 1 1 [] (by norm_num) p hp))).trans
        (le_of_eq (by ring))
  exact curvatureDriftError_bound_from_low_data g z p c (heightEnergyJetBound G Z)
    (hessianJetBound G Z d) (2 * christoffelJetBound G d) (G + Z)
    hc (hyy p hp) (hEB [] (by norm_num) p hp) (hHB [1] (by norm_num) p hp) ht
    (fun i j => (hgB i j [] (by norm_num) p hp).trans (by linarith))
    (fun i => (hzB [i] (by norm_num) p hp).trans (by linarith)) (hsmall p hp)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_HeightCapLowData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem heightCapCurvatureBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightCapCurvatureBound G Z d c := by
  have hK := curvatureFirstBound_nonneg hG hd
  have hF := flowCoordinateBound_nonneg (heightQuotientJetBound_nonneg hG hZ hd hc)
  unfold heightCapCurvatureBound
  positivity

theorem heightCapCoefficientBound_dominates {G Z d c e0 : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0) (ell : ℕ) :
    0 ≤ heightCapCoefficientBound G Z d c e0 ell ∧
    heightAJetBound G Z d c ≤ heightCapCoefficientBound G Z d c e0 ell ∧
    2*heightBJetBound G Z d c ell ≤ heightCapCoefficientBound G Z d c e0 ell ∧
    heightBJetBound G Z d c ell ≤ heightCapCoefficientBound G Z d c e0 ell ∧
    heightCapCValueBound G Z d c e0 ell ≤ heightCapCoefficientBound G Z d c e0 ell := by
  have hA := heightAJetBound_nonneg hG hZ hd hc
  have hB := heightBJetBound_nonneg hG hZ hd hc ell
  have hr := heightRemainderBound_nonneg hG hZ hd hc he0 ell
  have hC : 0 ≤ heightCapCValueBound G Z d c e0 ell := by
    unfold heightCapCValueBound
    positivity
  unfold heightCapCoefficientBound
  constructor
  · positivity
  constructor
  · linarith only [hB,hC]
  constructor
  · linarith only [hA,hC]
  constructor
  · linarith only [hA,hB,hC]
  · linarith only [hA,hB]

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_HeightNumericParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

theorem heightDirectedNumbers_spec {G Z d c e0 kappa : ℝ}
    (h : HeightNumericData G Z d c e0 kappa) (ell : ℕ) :
    HeightDirectedBudgets G Z d c e0 kappa ell (heightDirectedNumbers G Z d c e0 kappa ell) := by
  rw [heightDirectedNumbers,dite_eq_left h]
  exact Classical.choose_spec (exists_heightDirectedBudgets h ell)

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_UniformOriginalDataCapEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model SmoothLocal.HighEquation

def heightUniformCapEstimateRHS (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) (u f : Coord → ℝ) : ℝ :=
  let lambda := heightDirectedLambda G Z d c e0 kappa ell
  let c1 := heightDirectedSlope G Z d c e0 kappa ell
  let c2 := heightDirectedCoercivity G Z d c e0 kappa ell
  let M := heightCapCoefficientBound G Z d c e0 ell
  let MK := heightCapCurvatureBound G Z d c
  let glow := heightG1Lower G Z d c e0
  let MI := 2*heightBJetBound G Z d c ell
  let D := capDistanceBound bottom b
  let COverlap := capOverlapEnergyCost L R bottom b kappa c1 c2 glow M lambda MI
  let HElliptic := capEllipticRatioBudget L R bottom b kappa c1 glow MK M
  (2/(c2*capInteriorWeightFloor top b lambda MI))*
    ((((5/(2*c2))*(D^8*Real.exp (lambda*2+MI))+COverlap*D^6)*
      rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (f p)^2)) +
    ((COverlap*(D^6+HElliptic))*
      rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (u p)^2)))

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

theorem heightPhysicalCapConstant_pos (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) : 0 < heightPhysicalCapConstant G Z d c e0 kappa ell L R bottom top b := by
  unfold heightPhysicalCapConstant
  positivity

theorem heightUniformCapEstimateRHS_eq_factors (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) (u f : Coord → ℝ) :
    heightUniformCapEstimateRHS G Z d c e0 kappa ell L R bottom top b u f =
      (heightCapIntegralFactors G Z d c e0 kappa ell L R bottom top b).1*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (f p)^2)+
      (heightCapIntegralFactors G Z d c e0 kappa ell L R bottom top b).2*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (u p)^2) := by
  unfold heightUniformCapEstimateRHS heightCapIntegralFactors
  ring

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualRemainderRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry

theorem driftOperator_contDiffOn {q A B C u : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U) (hA : ContDiffOn ℝ ∞ A U)
    (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (driftOperator q A B C u) U := by
  have hDu := coordinateDrift_contDiffOn hq hu hU
  exact (((coordinateDrift_contDiffOn hq hDu hU).add
    (hA.mul (partial_contDiffOn (partial_contDiffOn hu hU 1) hU 1))).add
      (hB.mul hDu)).add (hC.mul (partial_contDiffOn hu hU 1))

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
open SmoothLocal.Geometry SmoothLocal.Analytic

def heightStateFactor (z : Coord → ℝ) (n : ℕ) (j : Fin 4) : Coord → ℝ :=
  ![coordPartial 0 (verticalJet z n), coordPartial 1 (verticalJet z n),
    coordPartial 0 (coordPartial 1 (verticalJet z n)),
    coordPartial 1 (coordPartial 1 (verticalJet z n))] j

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

def mixedFaaTerm (g : MetricField) (z : Coord → ℝ) {k : ℕ} (v : Fin k → Coord)
    (c : OrderedFinpartition k) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ c.length (sixVariableP g) (solutionJet z p)
    (fun j => iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p (v ∘ c.emb j))

def mixedFaaFactor (z : Coord → ℝ) {k : ℕ} (v : Fin k → Coord)
    (c : OrderedFinpartition k) (r : Fin c.length → Fin 6) (j : Fin c.length) (p : Coord) : ℝ :=
  (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p (v ∘ c.emb j)) (r j)

def mixedFaaRemainder (g : MetricField) (z : Coord → ℝ) {k : ℕ} (hk : 0 < k)
    (v : Fin k → Coord) (p : Coord) : ℝ :=
  heightPFirst g z 0 p * iteratedFDeriv ℝ k (coordPartial 0 z) p v +
  heightPFirst g z 1 p * iteratedFDeriv ℝ k (coordPartial 1 z) p v +
  ∑ c ∈ (Finset.univ.erase (fullBlockPartition k hk)), mixedFaaTerm g z v c p

theorem heightStateFactor_zero_eq_suffix (z : Coord → ℝ) (i : Fin 4) :
    heightStateFactor z 0 i = iteratedCoordPartial (heightStateSuffix i) z := by
  fin_cases i <;> rfl

theorem mixedFaaTerm_scalar_expansion (g : MetricField) (z : Coord → ℝ)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k) (p : Coord) :
    mixedFaaTerm g z v c p =
      ∑ r : Fin c.length → Fin 6,
        coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
          ∏ j, mixedFaaFactor z v c r j p :=
  multilinear_state_components _ _

theorem mixedFaaFactor_height_slot
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k) (j : Fin c.length)
    (i : Fin 4) :
    (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p (v ∘ c.emb j)) (heightComponentIndex i) =
      iteratedFDeriv ℝ (c.partSize j) (heightStateFactor z 0 i) p (v ∘ c.emb j) := by
  rw [state_fullJet_eval ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp))]
  fin_cases i <;> rfl

theorem mixedFaaFactor_spatial_slot
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k) (j : Fin c.length)
    (i : Fin 2) :
    (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p (v ∘ c.emb j))
        (if i = 0 then 0 else 1) =
      iteratedFDeriv ℝ (c.partSize j) (fun q : Coord => q i) p (v ∘ c.emb j) := by
  rw [state_fullJet_eval ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp))]
  fin_cases i <;> rfl

theorem mixed_fullBlock_term (g : MetricField) (z : Coord → ℝ) {k : ℕ}
    (hk : 0 < k) (v : Fin k → Coord) (p : Coord) :
    mixedFaaTerm g z v (fullBlockPartition k hk) p =
      fderiv ℝ (sixVariableP g) (solutionJet z p)
        (iteratedFDeriv ℝ k (solutionJet z) p v) := by
  change iteratedFDeriv ℝ 1 (sixVariableP g) (solutionJet z p)
    (fun _ : Fin 1 => iteratedFDeriv ℝ k (solutionJet z) p (v ∘ id)) = _
  rw [iteratedFDeriv_one_apply]
  rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_ActualRemainderL2
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def chainWordL2Budget (C B : ℝ) (H : ℝ≥0) (V : Set Coord) (ell : ℕ)
    (w : ChainWord) : ℝ≥0∞ :=
  ∑ _r : Fin w.arity → Fin 6, ‖C‖ₑ * chainProductL2Budget B H V ell

def chainSumL2Budget (C B : ℝ) (H : ℝ≥0) (V : Set Coord) (ell : ℕ)
    (ws : List ChainWord) : ℝ≥0∞ :=
  (ws.map (chainWordL2Budget C B H V ell)).sum

def actualHighRemainderL2Budget (C Cfirst B : ℝ) (H : ℝ≥0) (V : Set Coord)
    (m : ℕ) : ℝ≥0∞ :=
  chainSumL2Budget C B H V (m + 3) (topResidualWords m) +
    ‖(m + 3 : ℝ)‖ₑ * firstJetPairL2Budget Cfirst H

theorem chainWordL2Budget_lt_top (C B : ℝ) (H : ℝ≥0) {V : Set Coord}
    (hVfinite : volume V < (⊤ : ℝ≥0∞)) (ell : ℕ) (w : ChainWord) :
    chainWordL2Budget C B H V ell w < (⊤ : ℝ≥0∞) := by
  unfold chainWordL2Budget
  exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.mul_lt_top (by finiteness)
    (chainProductL2Budget_lt_top B H hVfinite ell))

theorem chainSumL2Budget_lt_top (C B : ℝ) (H : ℝ≥0) {V : Set Coord}
    (hVfinite : volume V < (⊤ : ℝ≥0∞)) (ell : ℕ) (ws : List ChainWord) :
    chainSumL2Budget C B H V ell ws < (⊤ : ℝ≥0∞) := by
  induction ws with
  | nil => simp [chainSumL2Budget]
  | cons w ws ih =>
      exact ENNReal.add_lt_top.mpr ⟨chainWordL2Budget_lt_top C B H hVfinite ell w, ih⟩

theorem actualHighRemainderL2Budget_lt_top (C Cfirst B : ℝ) (H : ℝ≥0)
    {V : Set Coord} (hVfinite : volume V < (⊤ : ℝ≥0∞)) (m : ℕ) :
    actualHighRemainderL2Budget C Cfirst B H V m < (⊤ : ℝ≥0∞) := by
  unfold actualHighRemainderL2Budget firstJetPairL2Budget
  exact ENNReal.add_lt_top.mpr
    ⟨chainSumL2Budget_lt_top C B H hVfinite (m + 3) (topResidualWords m), by finiteness⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_RemainderCoefficientBounds
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

theorem coordinateChainCoefficient_abs_le_full_derivative
    (g : MetricField) (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (p : Coord) :
    |coordinateChainCoefficient g z w r p| ≤
      ‖iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p)‖ := by
  have h := (iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p)).le_opNorm
    (fun i => Pi.single (r i) (1 : ℝ))
  simpa only [coordinateChainCoefficient, Pi.norm_single, norm_one,
    Finset.prod_const_one, mul_one, Real.norm_eq_abs] using h

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
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem mixedFaaFactor_continuousOn
    {z : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k)
    (r : Fin c.length → Fin 6) (j : Fin c.length) :
    ContinuousOn (mixedFaaFactor z v c r j) U :=
  (ContinuousLinearMap.proj (r j) : DarbouxState →L[ℝ] ℝ).continuous.comp_continuousOn
    (fullJet_fixed_input_continuousOn (solutionJet_contDiffOn hU hz) hU (c.partSize j) (v ∘ c.emb j))

theorem mixedBlock_spatial_abs_le_one
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (ds : List (Fin 2)) (c : OrderedFinpartition ds.length) (j : Fin c.length) (i : Fin 2) :
    |(iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
      (coordinateDirections ds ∘ c.emb j)) (if i = 0 then 0 else 1)| ≤ 1 := by
  rw [mixedFaaFactor_spatial_slot hU hz hp]
  have hd : (coordinateDirections ds ∘ c.emb j) = fun a => Pi.single (ds.get (c.emb j a)) (1 : ℝ) := by
    funext a
    exact coordinateDirections_apply ds (c.emb j a)
  rw [hd]
  exact fullJet_coordinate_projection_abs_le_one (c.partSize_pos j) _ i p

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MixedRemainderL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def mixedRemainderL2Budget (C B : ℝ) (H : ℝ≥0) (V : Set Coord) (k : ℕ) : ℝ≥0∞ :=
  firstJetPairL2Budget C H +
    ∑ c : OrderedFinpartition k, chainWordL2Budget C B H V k ⟨c.length, c.partSize⟩

theorem mixedRemainderL2Budget_lt_top (C B : ℝ) (H : ℝ≥0) {V : Set Coord}
    (hVfinite : volume V < (⊤ : ℝ≥0∞)) (k : ℕ) : mixedRemainderL2Budget C B H V k < (⊤ : ℝ≥0∞) := by
  unfold mixedRemainderL2Budget
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · unfold firstJetPairL2Budget
    finiteness
  · exact ENNReal.sum_lt_top.mpr (fun c _ =>
      chainWordL2Budget_lt_top C B H hVfinite k ⟨c.length, c.partSize⟩)

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
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem orderedPartial_replicate_y (z : Coord → ℝ) (n : ℕ) :
    iteratedCoordPartial (List.replicate n 1) z = verticalJet z n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, iteratedCoordPartial, verticalJet, ih]

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapL2Basics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem heightStateFactor_eq_ordered (z : Coord → ℝ) (n : ℕ) (j : Fin 4) :
    heightStateFactor z n j =
      iteratedCoordPartial (heightStateSuffix j ++ List.replicate n 1) z := by
  rw [orderedPartial_append, orderedPartial_replicate_y]
  fin_cases j <;> rfl

theorem coordinateBound_heightFactors {z : Coord → ℝ} {V : Set Coord} {N : ℕ} {B : ℝ}
    (h : CoordinateBound z V N B) (n : ℕ) (j : Fin 4)
    (hn : n + heightStateBaseOrder j ≤ N) :
    ∀ p ∈ V, |heightStateFactor z n j p| ≤ B := by
  rw [heightStateFactor_eq_ordered]
  apply h
  simpa only [List.length_append, List.length_replicate, heightStateSuffix_length, Nat.add_comm] using hn

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
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Analytic

theorem chainWordL2Budget_mono_area (C B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (ell : ℕ) (w : ChainWord) :
    chainWordL2Budget C B H V ell w ≤ chainWordL2Budget C B H W ell w := by
  apply Finset.sum_le_sum
  intro _ _
  exact mul_le_mul' le_rfl (chainProductL2Budget_mono_area B H hVW ell)

theorem chainSumL2Budget_mono_area (C B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (ell : ℕ) (ws : List ChainWord) :
    chainSumL2Budget C B H V ell ws ≤ chainSumL2Budget C B H W ell ws := by
  induction ws with
  | nil => exact le_rfl
  | cons word _ ih => exact add_le_add (chainWordL2Budget_mono_area C B H hVW ell word) ih

theorem actualHighRemainderL2Budget_mono_area (C Cfirst B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (m : ℕ) :
    actualHighRemainderL2Budget C Cfirst B H V m ≤ actualHighRemainderL2Budget C Cfirst B H W m :=
  add_le_add (chainSumL2Budget_mono_area C B H hVW (m+3) (topResidualWords m)) le_rfl

theorem mixedRemainderL2Budget_mono_area (C B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (k : ℕ) :
    mixedRemainderL2Budget C B H V k ≤ mixedRemainderL2Budget C B H W k := by
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro composition _
  exact chainWordL2Budget_mono_area C B H hVW k ⟨composition.length, composition.partSize⟩

def uniformMixedOrderBudget (C B : ℝ) (H Htop : ℝ≥0) (N : ℕ) : ℝ≥0 :=
  max H (mixedXBudget C (mixedRemainderL2Budget C B H modelSquare (N-2)) Htop N).toNNReal

theorem uniformMixedOrderBudget_coe (C B : ℝ) (H Htop : ℝ≥0) (N : ℕ) :
    (uniformMixedOrderBudget C B H Htop N : ℝ≥0∞) =
      max (H : ℝ≥0∞) (mixedXBudget C (mixedRemainderL2Budget C B H modelSquare (N-2)) Htop N) := by
  unfold uniformMixedOrderBudget
  rw [ENNReal.coe_max, ENNReal.coe_toNNReal
    (mixedXBudget_lt_top C
      (mixedRemainderL2Budget_lt_top C B H modelSquare_isCompact.measure_lt_top (N-2)) Htop N).ne]

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
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

variable {bStar : ℝ}

theorem lowerCapConstant_pos (G Z d c e0 kappa : ℝ) (ell : ℕ) (r : LowerCapRectangle bStar) :
    0 < lowerCapConstant G Z d c e0 kappa ell r :=
  heightPhysicalCapConstant_pos G Z d c e0 kappa ell r.left r.right r.bottom r.top ((r.top+bStar)/2)

end SmoothLocal.Flow

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

def LocalIsometric (g : MetricField) (U : Opens Coord) (F : U → Ambient) : Prop :=
  ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ F ∧
    ∀ p : U, ∀ v w : Coord,
      (inner ℝ : Ambient → Ambient → ℝ) (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) F p v)
        (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) F p w) =
          v ⬝ᵥ (g p *ᵥ w)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_UniversalMetricP
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

abbrev MetricPInput := MetricMatrix × (MetricFirstJet × (MetricSecondJet × DarbouxState))

def universalConnection (a : MetricPInput) (i j : Fin 2) : ℝ :=
  ∑ k, christoffelJet a.1 a.2.1 k i j * stateGradient a.2.2.2 k

def universalDenominator (a : MetricPInput) : ℝ :=
  a.2.2.2 5 - universalConnection a 1 1

def universalEnergy (a : MetricPInput) : ℝ :=
  a.1.det - (a.1 1 1 * (stateGradient a.2.2.2 0)^2 -
    (a.1 0 1 + a.1 1 0) * stateGradient a.2.2.2 0 * stateGradient a.2.2.2 1 +
    a.1 0 0 * (stateGradient a.2.2.2 1)^2)

def universalMetricP (a : MetricPInput) : ℝ :=
  universalConnection a 0 0 +
    ((a.2.2.2 4 - universalConnection a 0 1)^2 +
      curvatureJet a.1 a.2.1 a.2.2.1 * universalEnergy a) / universalDenominator a

def universalMetricBase : Set MetricPInput := {a | a.1.det ≠ 0}
def universalMetricDomain : Set MetricPInput :=
  {a | a.1.det ≠ 0 ∧ universalDenominator a ≠ 0}

def metricPBundle (g : MetricField) (w : DarbouxState) : MetricPInput :=
  (g (statePoint w),
    ((fun d i j => coordPartial d (fun p => g p i j) (statePoint w)),
      ((fun d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w)), w)))

theorem universalConnection_metricPBundle (g : MetricField) (w : DarbouxState)
    (i j : Fin 2) :
    universalConnection (metricPBundle g w) i j = stateConnection g i j w := rfl

theorem universalDenominator_metricPBundle (g : MetricField) (w : DarbouxState) :
    universalDenominator (metricPBundle g w) = stateDenominator g w := rfl

theorem universalEnergy_metricPBundle (g : MetricField) (w : DarbouxState) :
    universalEnergy (metricPBundle g w) = stateEnergy g w := rfl

theorem universalMetricDet_contDiff :
    ContDiff ℝ ∞ (fun a : MetricPInput => a.1.det) := by
  simp only [Matrix.det_fin_two]
  fun_prop

theorem universalMetricBase_isOpen : IsOpen universalMetricBase :=
  isOpen_ne_fun universalMetricDet_contDiff.continuous continuous_const

theorem universalConnection_contDiffAt {a : MetricPInput}
    (ha : a ∈ universalMetricBase) (i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun b => universalConnection b i j) a := by
  have hΓ (k : Fin 2) :
      ContDiffAt ℝ ∞ (fun b : MetricPInput => christoffelJet b.1 b.2.1 k i j) a :=
    christoffelJet_contDiffAt (fun i j => by fun_prop)
      (fun d i j => by fun_prop) ha k i j
  have hv (k : Fin 2) :
      ContDiffAt ℝ ∞ (fun b : MetricPInput => stateGradient b.2.2.2 k) a :=
    ((contDiff_apply ℝ ℝ k).comp
      (stateGradient_contDiff.comp (by fun_prop))).contDiffAt
  simp only [universalConnection, Fin.sum_univ_two]
  exact ((hΓ 0).mul (hv 0)).add ((hΓ 1).mul (hv 1))

theorem universalDenominator_contDiffOn :
    ContDiffOn ℝ ∞ universalDenominator universalMetricBase := by
  intro a ha
  exact ((show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 5) a by fun_prop).sub
    (universalConnection_contDiffAt ha 1 1)).contDiffWithinAt

theorem universalMetricDomain_isOpen : IsOpen universalMetricDomain := by
  exact universalDenominator_contDiffOn.continuousOn.isOpen_inter_preimage
    universalMetricBase_isOpen isClosed_singleton.isOpen_compl

theorem universalEnergy_contDiff : ContDiff ℝ ∞ universalEnergy := by
  unfold universalEnergy stateGradient
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [Matrix.det_fin_two]
  fun_prop

theorem universalMetricP_contDiffOn :
    ContDiffOn ℝ ∞ universalMetricP universalMetricDomain := by
  intro a ha
  have hΓ := universalConnection_contDiffAt ha.1
  have hK : ContDiffAt ℝ ∞
      (fun b : MetricPInput => curvatureJet b.1 b.2.1 b.2.2.1) a :=
    curvatureJet_contDiffAt (fun i j => by fun_prop)
      (fun d i j => by fun_prop) (fun d e i j => by fun_prop) ha.1
  have hm : ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4 - universalConnection b 0 1) a :=
    (show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4) a by fun_prop).sub (hΓ 0 1)
  exact ((hΓ 0 0).add (((hm.pow 2).add (hK.mul universalEnergy_contDiff.contDiffAt)).div
    (universalDenominator_contDiffOn.contDiffAt (universalMetricBase_isOpen.mem_nhds ha.1))
    ha.2)).contDiffWithinAt

def universalMetricBaseTube (M d : ℝ) : Set MetricPInput :=
  Metric.closedBall 0 M ∩ (fun a : MetricPInput => |a.1.det|) ⁻¹' Ici d

def universalMetricTube (M d c : ℝ) : Set MetricPInput :=
  universalMetricBaseTube M d ∩ universalDenominator ⁻¹' {x : ℝ | c ≤ |x|}

theorem universalMetricBaseTube_isCompact (M d : ℝ) :
    IsCompact (universalMetricBaseTube M d) :=
  (isCompact_closedBall (0 : MetricPInput) M).inter_right
    (isClosed_Ici.preimage universalMetricDet_contDiff.continuous.abs)

theorem universalMetricBaseTube_subset_base (M : ℝ) {d : ℝ} (hd : 0 < d) :
    universalMetricBaseTube M d ⊆ universalMetricBase := by
  intro a ha hz
  have hh : d ≤ |a.1.det| := ha.2
  rw [hz, abs_zero] at hh
  linarith

theorem universalMetricTube_isCompact (M : ℝ) {d : ℝ} (hd : 0 < d) (c : ℝ) :
    IsCompact (universalMetricTube M d c) := by
  have hbase := universalMetricBaseTube_isCompact M d
  have hc : ContinuousOn universalDenominator (universalMetricBaseTube M d) :=
    universalDenominator_contDiffOn.continuousOn.mono (universalMetricBaseTube_subset_base M hd)
  have hclosed : IsClosed (universalMetricTube M d c) :=
    hc.preimage_isClosed_of_isClosed hbase.isClosed (isClosed_le continuous_const continuous_abs)
  exact hbase.of_isClosed_subset hclosed inter_subset_left

theorem universalMetricTube_subset_domain (M : ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    universalMetricTube M d c ⊆ universalMetricDomain := by
  intro a ha
  refine ⟨universalMetricBaseTube_subset_base M hd ha.1, ?_⟩
  intro hz
  have hh : c ≤ |universalDenominator a| := ha.2
  rw [hz, abs_zero] at hh
  linarith

theorem universalMetricTube_finite_P_bounds (M : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ N, ∀ a ∈ universalMetricTube M d c,
      ‖iteratedFDeriv ℝ k universalMetricP a‖ ≤ C := by
  classical
  have hk : ∀ k : Fin (N + 1), ∃ A : ℝ,
      ∀ a ∈ universalMetricTube M d c, ‖iteratedFDeriv ℝ k.val universalMetricP a‖ ≤ A := by
    intro k
    have hcont : ContinuousOn (iteratedFDeriv ℝ k.val universalMetricP) universalMetricDomain := by
      apply (universalMetricP_contDiffOn.continuousOn_iteratedFDerivWithin
        (WithTop.coe_le_coe.mpr le_top) universalMetricDomain_isOpen.uniqueDiffOn).congr
      intro a ha
      exact (iteratedFDerivWithin_eq_iteratedFDeriv universalMetricDomain_isOpen.uniqueDiffOn
        ((universalMetricP_contDiffOn.contDiffAt
          (universalMetricDomain_isOpen.mem_nhds ha)).of_le (WithTop.coe_le_coe.mpr le_top)) ha).symm
    exact (universalMetricTube_isCompact M hd c).exists_bound_of_continuousOn
      (hcont.mono (universalMetricTube_subset_domain M hd hc))
  choose A hA using hk
  refine ⟨∑ k : Fin (N + 1), |A k|, Finset.sum_nonneg (fun k hk => abs_nonneg _), ?_⟩
  intro k hk a ha
  let j : Fin (N + 1) := ⟨k, by omega⟩
  exact (hA j a ha).trans ((le_abs_self (A j)).trans
    (Finset.single_le_sum (fun i hi => abs_nonneg (A i)) (Finset.mem_univ j)))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricPBundleBounds
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem norm_iteratedFDeriv_coordPartial_le {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (i : Fin 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (coordPartial i f) p‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) f p‖ := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) p :=
    (hf.fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hU.mem_nhds hp)
  have hh := norm_iteratedFDeriv_clm_apply_const (c := Pi.single i (1 : ℝ))
    hd (n := n) (WithTop.coe_le_coe.mpr le_top)
  have he : (fun y : Coord => fderiv ℝ f y (Pi.single i (1 : ℝ))) = coordPartial i f := by
    funext y
    rfl
  rw [he, Pi.norm_single, norm_one, one_mul, norm_iteratedFDeriv_fderiv] at hh
  exact hh

def statePointCLM : DarbouxState →L[ℝ] Coord :=
  ContinuousLinearMap.pi (fun i =>
    if i = 0 then ContinuousLinearMap.proj 0 else ContinuousLinearMap.proj 1)

theorem statePointCLM_eq (w : DarbouxState) : statePointCLM w = statePoint w := by
  ext i
  fin_cases i <;> simp [statePointCLM, statePoint]

theorem statePointCLM_norm_le : ‖statePointCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  rw [one_mul, statePointCLM_eq]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
  intro i
  fin_cases i
  · exact norm_le_pi_norm w 0
  · exact norm_le_pi_norm w 1

theorem norm_iteratedFDeriv_comp_statePoint {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v => f (statePoint v)) w‖ ≤
      ‖iteratedFDeriv ℝ n f (statePoint w)‖ := by
  have hp : statePointCLM w ∈ U := by
    rw [statePointCLM_eq]
    exact hw
  have hnumerical : ‖iteratedFDeriv ℝ n (f ∘ statePointCLM) w‖ ≤
      ‖iteratedFDeriv ℝ n f (statePointCLM w)‖ :=
    norm_iteratedFDeriv_comp_contraction statePointCLM hf hU statePointCLM_norm_le hp n
  have he : (fun v => f (statePoint v)) = f ∘ statePointCLM := by
    funext v
    change f (statePoint v) = f (statePointCLM v)
    rw [statePointCLM_eq]
  rw [he, ← statePointCLM_eq w]
  exact hnumerical

end SmoothLocal.HighEquation

end

end OAI
end


