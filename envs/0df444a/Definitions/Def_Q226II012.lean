-- Prove2me | Definitions.Def_Q226II012
-- name    : Q226II012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:48:27.622383+00:00
-- url     : https://prove2.me/theorems/7939d212-8006-422a-baf3-4c212df7a5ef
-- title:
--   Definitions bundle Q226II012 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 155 declarations of OpenAI's Lean: 11 definitions and 144 theorems. The definitions and types are `OAI.SmoothLocal.Geometry.patchTensorBudgetNeighborhood`, `OAI.SmoothLocal.Perturbation.affineTensorJetNeighborhood`, `OAI.SmoothLocal.Perturbation.boundedHeightClass`, `OAI.SmoothLocal.Perturbation.metricPatchSet`, `OAI.SmoothLocal.Perturbation.metricPositiveSet`, `OAI.SmoothLocal.Perturbation.patchObstructionSet`, `OAI.SmoothLocal.Perturbation.perturbationSeminorm`, `OAI.SmoothLocal.Perturbation.perturbationSeminormFamily`, `OAI.SmoothLocal.Perturbation.perturbedCurvatureJet`, `OAI.SmoothLocal.Perturbation.perturbedMetric`, `OAI.SmoothLocal.Pulse.supportedPulse`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Assembly_AssemblyProfiles`, `IsometricImmersion_Assembly_EnumeratedPatchTensors`, `IsometricImmersion_Assembly_InitialAssemblyMetric`, `IsometricImmersion_Assembly_SupportedMetricJets`, `IsometricImmersion_Assembly_SupportedNeighborhoods`, `IsometricImmersion_Assembly_SupportedPerturbations`, `IsometricImmersion_Calculus_BoundedClassInitialJet`, `IsometricImmersion_Calculus_MovingIntervalCalculus`, `IsometricImmersion_Calculus_ShearMetricJets`, `IsometricImmersion_Calculus_ShearedMetricFiniteJets`, `IsometricImmersion_Caps_BoundedClassCapData`, `IsometricImmersion_Comparison_BoundedClassApproximation`, `IsometricImmersion_Comparison_ClosureMetricApproximation`, `IsometricImmersion_Comparison_ComparisonCoefficientSmooth`, `IsometricImmersion_Comparison_ComparisonUpperVelocity`, `IsometricImmersion_Comparison_CurvatureFullJetComparison`, `IsometricImmersion_Comparison_FiniteApproximationJets`, `IsometricImmersion_Comparison_PulseClosureApproximation`, `IsometricImmersion_Coordinates_ActualCentralShearMargins`, `IsometricImmersion_Coordinates_ActualFiniteShearedCutBounds`, `IsometricImmersion_Coordinates_BoundedPatchSlabGeometry`, `IsometricImmersion_Coordinates_PatchAddressModel`, `IsometricImmersion_Curvature_InitialCurvature`, `IsometricImmersion_Curvature_PrescribedCurvature`, `IsometricImmersion_Darboux_CurvaturePrincipalPart`, `IsometricImmersion_Darboux_QActualSegmentTransfer`, `IsometricImmersion_Darboux_QCoefficientTube`, `IsometricImmersion_Darboux_QContainingRectangle`, `IsometricImmersion_Darboux_QFirstJetFunctions`, `IsometricImmersion_Darboux_QMetricDensityDecomposition`, `IsometricImmersion_Darboux_QMetricJetTransfer`, `IsometricImmersion_Darboux_QPositiveFloor`, `IsometricImmersion_Darboux_QPrincipal`, `IsometricImmersion_Darboux_QSpatialRestriction`, `IsometricImmersion_Darboux_SixVariableQ`, `IsometricImmersion_Darboux_SwappedDarboux`, `IsometricImmersion_Energy_ActualRemainderL2`, `IsometricImmersion_Energy_MovingEnergyPropagation`, `IsometricImmersion_Energy_MovingSlabEnergy`, `IsometricImmersion_Estimates_UniversalQRaw`, `IsometricImmersion_Immersions_ActualShearHeight`, `IsometricImmersion_Immersions_BoundedHeightClasses`, `IsometricImmersion_Metrics_ActualLowMetricBudget`, `IsometricImmersion_Metrics_ActualTestMetricPositive`, `IsometricImmersion_Metrics_AffineTensorNeighborhood`, `IsometricImmersion_Metrics_LocalMetricQFull`, `IsometricImmersion_Metrics_MetricPatchOpen`, `IsometricImmersion_Metrics_MetricQSpatialBundle`, `IsometricImmersion_Metrics_UniversalMetricQ`, `IsometricImmersion_Obstructions_BoundedClassTopology`, `IsometricImmersion_Obstructions_PatchObstructionSet`, `IsometricImmersion_Pulses_ActualPulseMetricCloseness`, `IsometricImmersion_Pulses_OffPulseMetricBounds`, `IsometricImmersion_Pulses_PulseDerivativeBounds`, `IsometricImmersion_Pulses_PulseEdgeReferenceDistance`, `IsometricImmersion_Pulses_PulseNeighborhood`, `IsometricImmersion_Pulses_PulseNeighborhoodAdapters`, `IsometricImmersion_Pulses_PulseProfiles`, `IsometricImmersion_Taylor_TaylorCoefficientBounds`, `IsometricImmersion_Taylor_TaylorResidual`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II007`, `Q226II008` and `Q226II009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q226II014`, `Q226II015` and `Q226II016`.
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
import Mathlib.Data.Nat.Choose.Sum
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
import Mathlib.Topology.GDelta.Basic
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

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_AssemblyProfiles
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter

namespace SmoothLocal.Geometry

theorem enumeratedAssemblyProfile_encode (i : AssemblyProfileIndex) :
    enumeratedAssemblyProfile (Encodable.encode i) = assemblyProfile i := by
  simp only [enumeratedAssemblyProfile, Encodable.decode₂_encode]

theorem enumeratedAssemblyProfile_zero_other (i : AssemblyProfileIndex) {p : Coord}
    (hp : p ∈ assemblyCarrier i) {j : ℕ} (hj : j ≠ Encodable.encode i) :
    enumeratedAssemblyProfile j p = 0 := by
  cases hd : Encodable.decode₂ AssemblyProfileIndex j with
  | none => simp [enumeratedAssemblyProfile, hd]
  | some a =>
      have ha : a ≠ i := by
        intro hai
        subst a
        exact hj (Encodable.decode₂_eq_some.mp hd).symm
      have hnot : p ∉ tsupport (assemblyProfile a) := fun hpa =>
        Set.disjoint_left.mp (assemblyCarriers_pairwise_disjoint ha)
          (assemblyProfile_tsupport_subset a hpa) hp
      have hz : assemblyProfile a p = 0 := by
        by_contra hne
        exact hnot (subset_tsupport (assemblyProfile a) hne)
      simpa only [enumeratedAssemblyProfile, hd] using hz

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_PrescribedCurvature
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem prescribedFactor_firstPartial {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    {p : Coord} (hp : p ∈ square) :
    coordPartial 0 (prescribedFactor K) p = (globalPrescribedState K (p 0, p 1)).2 := by
  have hd := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt (p 0)
    (globalPrescribedState_hasDerivAt hK hbound (hp 0) (hp 1))
  have hd' : HasDerivAt (fun t => prescribedFactor K (coordinatePoint t (p 1)))
      (globalPrescribedState K (p 0, p 1)).2 (p 0) := by
    simpa [Function.comp_def, prescribedFactor, globalPrescribedScalar, coordinatePoint,
      curvatureField] using hd
  exact (coordinateSlice_hasDerivAt_x (prescribedFactor_contDiffOn hK hbound) hp).unique hd'

theorem prescribedFactor_secondPartial {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    {p : Coord} (hp : p ∈ square) :
    coordPartial 0 (coordPartial 0 (prescribedFactor K)) p = -K p * prescribedFactor K p := by
  have hd := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt (p 0)
    (globalPrescribedState_hasDerivAt hK hbound (hp 0) (hp 1))
  have hd' : HasDerivAt (fun t => (globalPrescribedState K (t, p 1)).2)
      (-K p * prescribedFactor K p) (p 0) := by
    simpa [Function.comp_def, curvatureField, coordinatePoint_eta, prescribedFactor,
      globalPrescribedScalar] using hd
  have hev : (fun t => coordPartial 0 (prescribedFactor K) (coordinatePoint t (p 1)))
      =ᶠ[𝓝 (p 0)] (fun t => (globalPrescribedState K (t, p 1)).2) := by
    filter_upwards [isOpen_Ioo.mem_nhds (hp 0)] with t ht
    simpa [coordinatePoint] using prescribedFactor_firstPartial hK hbound
      (coordinatePoint_mem_square ht (hp 1))
  have hpartial : ContDiffOn ℝ ∞ (coordPartial 0 (prescribedFactor K)) square :=
    partial_contDiffOn (prescribedFactor_contDiffOn hK hbound) coordinate_square_isOpen 0
  exact (coordinateSlice_hasDerivAt_x hpartial hp).unique (hd'.congr_of_eventuallyEq hev)

theorem prescribedCurvatureMetric_smoothPositiveOn {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000) :
    SmoothPositiveOn (prescribedCurvatureMetric K) square :=
  warpedMetric_smoothPositiveOn (prescribedFactor_contDiffOn hK hbound)
    (fun _ hp => ne_of_gt (prescribedFactor_bounds hK hbound hp).2.2)

theorem prescribedCurvatureMetric_gaussianCurvature {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    {p : Coord} (hp : p ∈ square) :
    gaussianCurvature (prescribedCurvatureMetric K) p = K p := by
  have hne : ∀ q ∈ square, prescribedFactor K q ≠ 0 :=
    fun q hq => ne_of_gt (prescribedFactor_bounds hK hbound hq).2.2
  rw [prescribedCurvatureMetric,
    gaussianCurvature_warpedMetric (prescribedFactor_contDiffOn hK hbound)
      coordinate_square_isOpen hne hp,
    prescribedFactor_secondPartial hK hbound hp]
  field_simp [hne p hp]

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

theorem perturbationTensor_symmetric (η : SymmetricPerturbation) (p : Coord) (i j : Fin 2) :
    perturbationTensor η p i j = perturbationTensor η p j i := η.property p i j

theorem perturbationTensor_contDiff (η : SymmetricPerturbation) :
    ContDiff ℝ ∞ (perturbationTensor η) := η.val.contDiff

theorem perturbationTensor_coeff_contDiff (η : SymmetricPerturbation) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun p => perturbationTensor η p i j) :=
  (contDiff_apply ℝ ℝ j).comp
    ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (perturbationTensor_contDiff η))

theorem perturbationTensor_zero_off_patch (η : SymmetricPerturbation)
    {p : Coord} (hp : p ∉ patchBox) : perturbationTensor η p = 0 := η.val.zero_on_compl hp

def perturbationSeminorm (k : ℕ) (η : SymmetricPerturbation) : ℝ :=
  ContDiffMapSupportedIn.seminorm ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ) ⊤ patchCompact k η.val

theorem perturbationSeminorm_continuous (k : ℕ) : Continuous (perturbationSeminorm k) :=
  ((ContDiffMapSupportedIn.withSeminorms ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ)
    ⊤ patchCompact).continuous_seminorm k).comp continuous_subtype_val

theorem perturbation_derivative_norm_le (η : SymmetricPerturbation) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (perturbationTensor η) p‖ ≤ perturbationSeminorm k η :=
  ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ

def perturbedMetric (g0 : MetricField) (η : SymmetricPerturbation) : MetricField :=
  g0 + perturbationTensor η

def metricPatchSet (g0 : MetricField) (kappa : ℝ) : Set SymmetricPerturbation :=
  {η | (∀ p ∈ modelSquare, (perturbedMetric g0 η p).PosDef) ∧
    ∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 η) p < -kappa / 2}

theorem perturbedMetric_smoothPositiveOn {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (η : SymmetricPerturbation)
    (hpos : ∀ p ∈ modelSquare, (perturbedMetric g0 η p).PosDef) :
    SmoothPositiveOn (perturbedMetric g0 η) U := by
  constructor
  · intro i j
    exact (hg0.1 i j).add (perturbationTensor_coeff_contDiff η i j).contDiffOn
  · intro p hp
    by_cases hP : p ∈ patchBox
    · exact hpos p (patchBox_subset_modelSquare hP)
    · simpa only [perturbedMetric, Pi.add_apply, perturbationTensor_zero_off_patch η hP,
        add_zero] using hg0.2 p hp

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_SupportedNeighborhoods
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

def perturbationSeminormFamily : ℕ → Seminorm ℝ SymmetricPerturbation := fun k =>
  (ContDiffMapSupportedIn.seminorm ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ) ⊤ patchCompact k).comp
    symmetricSupportedSubmodule.subtype

theorem symmetricPerturbation_withSeminorms : WithSeminorms perturbationSeminormFamily :=
  Topology.IsInducing.withSeminorms
    (ContDiffMapSupportedIn.withSeminorms ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ) ⊤ patchCompact)
    (f := symmetricSupportedSubmodule.subtype) .subtypeVal

theorem exists_finite_seminorm_neighborhood {O : Set SymmetricPerturbation}
    (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O) :
    ∃ (s : Finset ℕ) (epsilon : ℝ), 0 < epsilon ∧
      ∀ ρ : SymmetricPerturbation,
        (∀ k ∈ s, perturbationSeminorm k ρ < epsilon) → η + ρ ∈ O := by
  obtain ⟨s, epsilon, heps, hsub⟩ :=
    (symmetricPerturbation_withSeminorms.mem_nhds_iff η O).mp (hO.mem_nhds hη)
  refine ⟨s, epsilon, heps, ?_⟩
  intro ρ hρ
  apply hsub
  rw [Seminorm.mem_ball]
  simpa only [add_sub_cancel_left] using
    Seminorm.finset_sup_apply_lt heps
      (show ∀ k ∈ s, perturbationSeminormFamily k ρ < epsilon from hρ)

theorem exists_ordered_seminorm_neighborhood {O : Set SymmetricPerturbation}
    (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O) :
    ∃ (N : ℕ) (epsilon : ℝ), 10 < N ∧ 0 < epsilon ∧
      ∀ ρ : SymmetricPerturbation,
        (∀ k < N, perturbationSeminorm k ρ < epsilon) → η + ρ ∈ O := by
  obtain ⟨s, epsilon, heps, hsub⟩ := exists_finite_seminorm_neighborhood hO hη
  let N : ℕ := max 11 (s.sup id + 1)
  have hN : 10 < N :=
    lt_of_lt_of_le (by norm_num : 10 < (11 : ℕ)) (le_max_left _ _)
  refine ⟨N, epsilon, hN, heps, ?_⟩
  intro ρ hρ
  apply hsub ρ
  intro k hk
  have hkSup : k ≤ s.sup id := by
    simpa only [id_eq] using (Finset.le_sup (f := id) hk)
  exact hρ k (lt_of_lt_of_le (Nat.lt_succ_of_le hkSup) (le_max_right _ _))

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_AffineTensorNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

def affineTensorJetNeighborhood (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ)
    (epsilon : ℝ) : Set SymmetricPerturbation :=
  {η | ∀ k : Fin (N+1),
    perturbationSeminorm k.val η < epsilon / affineTensorOrderFactor R N}

theorem affineTensorJetNeighborhood_isOpen
    (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ) (epsilon : ℝ) :
    IsOpen (affineTensorJetNeighborhood R N epsilon) := by
  unfold affineTensorJetNeighborhood
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro k
  exact isOpen_lt (perturbationSeminorm_continuous k.val) continuous_const

theorem zero_mem_affineTensorJetNeighborhood
    (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (0 : SymmetricPerturbation) ∈ affineTensorJetNeighborhood R N epsilon := by
  intro k
  have hzero : perturbationSeminorm k.val 0 = 0 := map_zero (perturbationSeminormFamily k.val)
  rw [hzero]
  exact div_pos hepsilon (affineTensorOrderFactor_pos R N)

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

def patchTensorBudgetNeighborhood (epsilon : ℝ) (a : PatchAddress) : Set SymmetricPerturbation :=
  affineTensorJetNeighborhood (patchAddressMatrix a) (patchTensorIndex a)
    (patchSeriesWeight epsilon (patchTensorIndex a))

theorem patchTensorBudgetNeighborhood_isOpen (epsilon : ℝ) (a : PatchAddress) :
    IsOpen (patchTensorBudgetNeighborhood epsilon a) :=
  affineTensorJetNeighborhood_isOpen _ _ _

theorem zero_mem_patchTensorBudgetNeighborhood {epsilon : ℝ} (he : 0 < epsilon) (a : PatchAddress) :
    (0 : SymmetricPerturbation) ∈ patchTensorBudgetNeighborhood epsilon a :=
  zero_mem_affineTensorJetNeighborhood _ _ (patchSeriesWeight_pos he _)

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

theorem initialCurvature_eq_profile (i : AssemblyProfileIndex) {p : Coord}
    (hp : p ∈ assemblyCarrier i) : initialCurvature p =
      initialCurvatureAmplitudes (Encodable.encode i) * assemblyProfile i p := by
  change (∑' j, initialCurvatureTerm j p) = _
  rw [tsum_eq_single (Encodable.encode i)]
  · simp only [initialCurvatureTerm, enumeratedAssemblyProfile_encode, smul_eq_mul]
  · intro j hj
    simp only [initialCurvatureTerm, enumeratedAssemblyProfile_zero_other i hp hj, smul_zero]

theorem initialCurvature_model_on_patch (n k : ℕ) (R : OrientationLabel) (c : Coord)
    (hc : c ∈ orientedExteriorCenters n k R) {q : Coord} (hq : ‖q‖ ≤ 13 / 4) :
    initialCurvature (affineCoordinates c (orientedPatchScale n k R • R.val) q) =
      initialPatchAmplitude n k R c hc * ((q 0) ^ 2 - modelProfile (q 1)) := by
  have hbox : q ∈ closedPatchBox := (mem_closedPatchBox_iff_norm_le q).mpr (by linarith)
  have hcarrier : affineCoordinates c (orientedPatchScale n k R • R.val) q ∈
      assemblyCarrier (Sum.inr ⟨n, k, R, c, hc⟩) := ⟨q, hbox, rfl⟩
  rw [initialCurvature_eq_profile (Sum.inr ⟨n, k, R, c, hc⟩) hcarrier]
  change initialPatchAmplitude n k R c hc *
    localPatchProfile (affineInverseCoordinates c (orientedPatchScale n k R • R.val)
      (affineCoordinates c (orientedPatchScale n k R • R.val) q)) = _
  rw [affineInverseCoordinates_affineCoordinates c _ (orientedPatchMatrix_isUnit n k R),
    localPatchProfile_eq_model hq]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_InitialAssemblyMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set

namespace SmoothLocal.Geometry
open SmoothLocal.ODE SmoothLocal.Model

theorem initialAssemblyMetric_smoothPositiveOn :
    SmoothPositiveOn initialAssemblyMetric square :=
  prescribedCurvatureMetric_smoothPositiveOn initialCurvature_contDiff.contDiffOn
    (fun p _ => initialCurvature_small p)

theorem initialAssemblyMetric_gaussianCurvature {p : Coord} (hp : p ∈ square) :
    gaussianCurvature initialAssemblyMetric p = initialCurvature p :=
  prescribedCurvatureMetric_gaussianCurvature initialCurvature_contDiff.contDiffOn
    (fun p _ => initialCurvature_small p) hp

theorem patch_core_image_mem_square (n k : ℕ) (R : OrientationLabel) (c : Coord)
    (hc : c ∈ orientedExteriorCenters n k R) {q : Coord} (hq : ‖q‖ ≤ 13 / 4) :
    affineCoordinates c (orientedPatchScale n k R • R.val) q ∈ square := by
  apply orientedClosedPatch_subset_square n k R hc
  exact ⟨q, (mem_closedPatchBox_iff_norm_le q).mpr (by linarith), rfl⟩

theorem initialAssemblyMetric_model_in_physical_coordinates (n k : ℕ)
    (R : OrientationLabel) (c : Coord) (hc : c ∈ orientedExteriorCenters n k R)
    {q : Coord} (hq : ‖q‖ ≤ 13 / 4) :
    gaussianCurvature initialAssemblyMetric
      (affineCoordinates c (orientedPatchScale n k R • R.val) q) =
        initialPatchAmplitude n k R c hc * ((q 0) ^ 2 - modelProfile (q 1)) := by
  rw [initialAssemblyMetric_gaussianCurvature (patch_core_image_mem_square n k R c hc hq)]
  exact initialCurvature_model_on_patch n k R c hc hq

theorem initialAssemblyMetric_model_in_patch_coordinates (n k : ℕ)
    (R : OrientationLabel) (c : Coord) (hc : c ∈ orientedExteriorCenters n k R)
    {q : Coord} (hq : ‖q‖ ≤ 13 / 4) :
    gaussianCurvature (affinePullbackMetric initialAssemblyMetric c
      (orientedPatchScale n k R • R.val)) q =
        modelCurvature (initialPatchAmplitude n k R c hc) q := by
  rw [gaussianCurvature_affinePullback initialAssemblyMetric_smoothPositiveOn
    coordinate_square_isOpen c _ (orientedPatchMatrix_isUnit n k R) q
      (patch_core_image_mem_square n k R c hc hq)]
  exact initialAssemblyMetric_model_in_physical_coordinates n k R c hc hq

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_SupportedMetricJets
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem perturbationTensor_coeff_eval_joint_continuous (i j : Fin 2) :
    Continuous (fun a : SymmetricPerturbation × Coord => perturbationTensor a.1 a.2 i j) :=
  (supportedTensor_coeff_eval_joint_continuous i j).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem perturbationTensor_coordPartial_joint_continuous (d i j : Fin 2) :
    Continuous (fun a : SymmetricPerturbation × Coord =>
      coordPartial d (fun q => perturbationTensor a.1 q i j) a.2) :=
  (supportedTensor_coordPartial_joint_continuous d i j).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem perturbationTensor_second_coordPartial_joint_continuous (d e i j : Fin 2) :
    Continuous (fun a : SymmetricPerturbation × Coord =>
      coordPartial d (coordPartial e (fun q => perturbationTensor a.1 q i j)) a.2) :=
  (supportedTensor_second_coordPartial_joint_continuous d e i j).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem perturbedMetric_coordPartial {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (η : SymmetricPerturbation)
    {p : Coord} (hp : p ∈ U) (d i j : Fin 2) :
    coordPartial d (fun q => perturbedMetric g0 η q i j) p =
      coordPartial d (fun q => g0 q i j) p +
        coordPartial d (fun q => perturbationTensor η q i j) p := by
  apply HessianCalculus.coordPartial_add_at
  · exact (((hg0.1 i j) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact (perturbationTensor_coeff_contDiff η i j).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p

theorem perturbedMetric_second_coordPartial {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (η : SymmetricPerturbation)
    {p : Coord} (hp : p ∈ U) (d e i j : Fin 2) :
    coordPartial d (coordPartial e (fun q => perturbedMetric g0 η q i j)) p =
      coordPartial d (coordPartial e (fun q => g0 q i j)) p +
        coordPartial d (coordPartial e (fun q => perturbationTensor η q i j)) p := by
  have heq : coordPartial e (fun q => perturbedMetric g0 η q i j) =ᶠ[𝓝 p]
      (fun q => coordPartial e (fun q => g0 q i j) q +
        coordPartial e (fun q => perturbationTensor η q i j) q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact perturbedMetric_coordPartial hg0 hU η hq e i j
  change fderiv ℝ _ p (Pi.single d 1) = _
  rw [heq.fderiv_eq]
  apply HessianCalculus.coordPartial_add_at
  · exact (((partial_contDiffOn (hg0.1 i j) hU e) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact (((partial_contDiffOn (perturbationTensor_coeff_contDiff η i j).contDiffOn
      isOpen_univ e) p (mem_univ p)).contDiffAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

section JointMetric
variable {g0 : MetricField} {U : Set Coord}
variable (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U)
variable {η : SymmetricPerturbation} {p : Coord} (hp : p ∈ U)
include hg0 hU hp

theorem perturbedMetric_coeff_joint_continuousAt (i j : Fin 2) :
    ContinuousAt (fun a : SymmetricPerturbation × Coord => perturbedMetric g0 a.1 a.2 i j)
      (η, p) := by
  have hbg := (((hg0.1 i j) p hp).contDiffAt (hU.mem_nhds hp)).continuousAt
  exact (hbg.comp (x := (η, p)) continuous_snd.continuousAt).add
    (perturbationTensor_coeff_eval_joint_continuous i j).continuousAt

theorem perturbedMetric_coordPartial_joint_continuousAt (d i j : Fin 2) :
    ContinuousAt (fun a : SymmetricPerturbation × Coord =>
      coordPartial d (fun q => perturbedMetric g0 a.1 q i j) a.2) (η, p) := by
  have hbg := (((partial_contDiffOn (hg0.1 i j) hU d) p hp).contDiffAt
    (hU.mem_nhds hp)).continuousAt
  have hc := (hbg.comp (x := (η, p)) continuous_snd.continuousAt).add
    (perturbationTensor_coordPartial_joint_continuous d i j).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)] with a ha
  exact perturbedMetric_coordPartial hg0 hU a.1 ha d i j

theorem perturbedMetric_second_coordPartial_joint_continuousAt (d e i j : Fin 2) :
    ContinuousAt (fun a : SymmetricPerturbation × Coord =>
      coordPartial d (coordPartial e (fun q => perturbedMetric g0 a.1 q i j)) a.2) (η, p) := by
  have hbg := (((partial_contDiffOn (partial_contDiffOn (hg0.1 i j) hU e) hU d)
    p hp).contDiffAt (hU.mem_nhds hp)).continuousAt
  have hc := (hbg.comp (x := (η, p)) continuous_snd.continuousAt).add
    (perturbationTensor_second_coordPartial_joint_continuous d e i j).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)] with a ha
  exact perturbedMetric_second_coordPartial hg0 hU a.1 ha d e i j

end JointMetric

def perturbedCurvatureJet (g0 : MetricField) (η : SymmetricPerturbation) (p : Coord) : ℝ :=
  curvatureJet (perturbedMetric g0 η p)
    (fun d i j => coordPartial d (fun q => perturbedMetric g0 η q i j) p)
    (fun d e i j => coordPartial d (coordPartial e (fun q => perturbedMetric g0 η q i j)) p)

theorem perturbedCurvatureJet_joint_continuousAt {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) {η : SymmetricPerturbation}
    {p : Coord} (hp : p ∈ U) (hdet : (perturbedMetric g0 η p).det ≠ 0) :
    ContinuousAt (fun a : SymmetricPerturbation × Coord => perturbedCurvatureJet g0 a.1 a.2)
      (η, p) :=
  curvatureJet_continuousAt (perturbedMetric_coeff_joint_continuousAt hg0 hU hp)
    (perturbedMetric_coordPartial_joint_continuousAt hg0 hU hp)
    (perturbedMetric_second_coordPartial_joint_continuousAt hg0 hU hp) hdet

theorem gaussianCurvature_perturbedMetric_eq_jet {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (η : SymmetricPerturbation)
    (hpos : ∀ p ∈ modelSquare, (perturbedMetric g0 η p).PosDef)
    {p : Coord} (hp : p ∈ U) :
    gaussianCurvature (perturbedMetric g0 η) p = perturbedCurvatureJet g0 η p :=
  gaussianCurvature_eq_curvatureJet (perturbedMetric_smoothPositiveOn hg0 η hpos) hU hp

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_SwappedDarboux
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

theorem jetConnection_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (i j : Fin 2) (u : Coord) :
    jetConnection (swappedMetric g) p i j (coordinateSwap u) =
      jetConnection g (coordinateSwap p) (swapCoordinateIndex i) (swapCoordinateIndex j) u := by
  simp only [jetConnection, christoffel_swappedMetric hg hU hp,
    coordinateSwap_apply, Fin.sum_univ_two, swapCoordinateIndex_zero, swapCoordinateIndex_one]
  ring

theorem jetMixed_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (b : ℝ) (u : Coord) :
    jetMixed (swappedMetric g) p b (coordinateSwap u) =
      jetMixed g (coordinateSwap p) b u := by
  have hs (k : Fin 2) : christoffel g k 1 0 (coordinateSwap p) =
      christoffel g k 0 1 (coordinateSwap p) := christoffel_lower_symm hg hU hp k 1 0
  rw [jetMixed, jetConnection_swappedMetric hg hU hp]
  simp only [swapCoordinateIndex_zero, swapCoordinateIndex_one]
  simp only [jetConnection, hs, jetMixed]

theorem jetYY_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (c : ℝ) (u : Coord) :
    jetYY (swappedMetric g) p c (coordinateSwap u) =
      jetXX g (coordinateSwap p) c u := by
  rw [jetYY, jetConnection_swappedMetric hg hU hp]
  rfl

theorem jetNumerator_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (b : ℝ) (u : Coord) :
    jetNumerator (swappedMetric g) p b (coordinateSwap u) =
      jetNumerator g (coordinateSwap p) b u := by
  rw [jetNumerator, jetMixed_swappedMetric hg hU hp,
    gaussianCurvature_swappedMetric hg hU hp, jetEnergy_swappedMetric]
  rfl

theorem solvedDarboux_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (b c : ℝ) (u : Coord) :
    solvedDarboux (swappedMetric g) p b c (coordinateSwap u) =
      solvedDarbouxQ g (coordinateSwap p) b c u := by
  rw [solvedDarboux, jetConnection_swappedMetric hg hU hp,
    jetNumerator_swappedMetric hg hU hp, jetYY_swappedMetric hg hU hp]
  rfl

theorem solvedDarbouxQ_eq_swappedP {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ U) (b c : ℝ) (u : Coord) :
    solvedDarbouxQ g p b c u =
      solvedDarboux (swappedMetric g) (coordinateSwap p) b c (coordinateSwap u) := by
  simpa only [coordinateSwap_involutive] using
    (solvedDarboux_swappedMetric hg hU (p := coordinateSwap p) (by simpa using hp) b c u).symm

theorem solvedDarbouxQ_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    coordPartial 1 (coordPartial 1 z) p =
      solvedDarbouxQ g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p) := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  have hsolve : covHessian g z p 1 1 =
      ((covHessian g z p 0 1) ^ 2 + gaussianCurvature g p * heightEnergy g z p) /
        covHessian g z p 0 0 := by
    apply (eq_div_iff hxx).2
    nlinarith [hdet]
  change coordPartial 1 (coordPartial 1 z) p -
    jetConnection g p 1 1 (fun i => coordPartial i z p) = _ at hsolve
  rw [solvedDarbouxQ, jetNumerator, jetMixed_at_height, jetXX_at_height,
    jetEnergy_at_height hg hp z]
  linarith [hsolve]

theorem darbouxDet_of_solvedQ_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0)
    (hQ : coordPartial 1 (coordPartial 1 z) p =
      solvedDarbouxQ g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p)) :
    (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p := by
  rw [solvedDarbouxQ, jetNumerator, jetMixed_at_height, jetXX_at_height,
    jetEnergy_at_height hg hp z] at hQ
  have hsolve : covHessian g z p 1 1 =
      ((covHessian g z p 0 1) ^ 2 + gaussianCurvature g p * heightEnergy g z p) /
        covHessian g z p 0 0 := by
    change coordPartial 1 (coordPartial 1 z) p -
      jetConnection g p 1 1 (fun i => coordPartial i z p) = _
    linarith [hQ]
  have hmul := (eq_div_iff hxx).1 hsolve
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    nlinarith [hmul]
  simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hdet

theorem darbouxDet_iff_solvedQ_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p ↔
      coordPartial 1 (coordPartial 1 z) p =
        solvedDarbouxQ g p (coordPartial 0 (coordPartial 1 z) p)
          (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p) :=
  ⟨solvedDarbouxQ_at_height hg hU hz hp hxx,
    darbouxDet_of_solvedQ_at_height hg hU hz hp hxx⟩

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_SixVariableQ
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem stateDenominator_qToPState {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    stateDenominator (swappedMetric g) (qToPState w) = stateQDenominator g w := by
  unfold stateDenominator
  rw [statePoint_qToPState, stateGradient_qToPState, qToPState_five]
  simpa only [stateQDenominator, coordinateSwap_involutive] using
    (jetYY_swappedMetric hg hU (p := coordinateSwap (statePoint w))
      (by simpa using hw) (w 5) (stateGradient w))

theorem sixVariableQ_explicit {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    sixVariableQ g w =
      solvedDarbouxQ g (statePoint w) (w 4) (w 5) (stateGradient w) := by
  unfold sixVariableQ sixVariableP
  simp only [Function.comp_apply, statePoint_qToPState, stateGradient_qToPState,
    qToPState_four, qToPState_five]
  exact (solvedDarbouxQ_eq_swappedP hg hU hw (w 4) (w 5) (stateGradient w)).symm

theorem darbouxQStateDomain_eq_preimage {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    darbouxQStateDomain g U =
      qToPState ⁻¹' darbouxStateDomain (swappedMetric g) (coordinateSwap ⁻¹' U) := by
  ext w
  constructor
  · intro hw
    refine ⟨?_, ?_⟩
    · simpa only [Set.mem_preimage, statePoint_qToPState, coordinateSwap_involutive] using hw.1
    · simpa only [stateDenominator_qToPState hg hU hw.1] using hw.2
  · intro hw
    have hp : statePoint w ∈ U := by
      simpa only [Set.mem_preimage, statePoint_qToPState, coordinateSwap_involutive] using hw.1
    exact ⟨hp, by simpa only [stateDenominator_qToPState hg hU hp] using hw.2⟩

theorem qToPState_mem_domain {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    qToPState w ∈ darbouxStateDomain (swappedMetric g) (coordinateSwap ⁻¹' U) := by
  simpa only [darbouxQStateDomain_eq_preimage hg hU, Set.mem_preimage] using hw

theorem darbouxQStateDomain_isOpen {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) : IsOpen (darbouxQStateDomain g U) := by
  rw [darbouxQStateDomain_eq_preimage hg hU]
  exact (darbouxStateDomain_isOpen (swappedMetric_smoothPositive hg)
    (coordinateSwap_preimage_isOpen hU)).preimage qToPState_contDiff.continuous

theorem sixVariableQ_update_mixed {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) (t : ℝ) :
    sixVariableQ g (Function.update w 4 t) =
      solvedDarbouxQ g (statePoint w) t (w 5) (stateGradient w) := by
  have hp : statePoint (Function.update w 4 t) = statePoint w := by
    ext j
    fin_cases j <;> simp [statePoint]
  have hv : stateGradient (Function.update w 4 t) = stateGradient w := by
    ext j
    fin_cases j <;> simp [stateGradient]
  rw [sixVariableQ_explicit hg hU (by simpa only [hp] using hw), hp, hv]
  simp

theorem sixVariableQ_update_xx {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) (t : ℝ) :
    sixVariableQ g (Function.update w 5 t) =
      solvedDarbouxQ g (statePoint w) (w 4) t (stateGradient w) := by
  have hp : statePoint (Function.update w 5 t) = statePoint w := by
    ext j
    fin_cases j <;> simp [statePoint]
  have hv : stateGradient (Function.update w 5 t) = stateGradient w := by
    ext j
    fin_cases j <;> simp [stateGradient]
  rw [sixVariableQ_explicit hg hU (by simpa only [hp] using hw), hp, hv]
  simp

theorem darbouxDet_iff_sixVariableQ {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p ↔
      coordPartial 1 (coordPartial 1 z) p = sixVariableQ g (qSolutionJet z p) := by
  rw [sixVariableQ_explicit hg hU (by simpa only [statePoint_qSolutionJet] using hp),
    statePoint_qSolutionJet, stateGradient_qSolutionJet]
  exact darbouxDet_iff_solvedQ_at_height hg hU hz hp hxx

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

theorem gaussianCurvature_density_principal_part {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    gaussianCurvature g p * (g p).det =
      coordPartial 0 (coordPartial 1 (fun q => g q 0 1)) p -
        (coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p +
          coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p)/2 +
        curvatureLowerTerm g p := by
  have hraw := curvatureJet_density_raw (g p) (metricFirstJet g p)
    (fun (d e i j : Fin 2) => coordPartial d (coordPartial e (fun q => g q i j)) p)
    (metricDet_ne_zero hg hp)
  have hfull := (congrArg (fun k : ℝ => k * (g p).det)
    (gaussianCurvature_eq_curvatureJet hg hU hp)).trans hraw
  rw [metric_coeff_second_partial_symm hg hU hp 0 1 1 0,
    metric_coeff_second_partial_symm hg hU hp 1 0 1 0,
    coordPartial_comm (hg.1 0 1) hU hp 1 0] at hfull
  rw [hfull]
  dsimp only [curvatureLowerTerm,metricFirstJet]
  ring

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

def supportedPulse (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    (ha : 0 < a) (hd : 0 < delta) (ht : 0 < tau)
    (hax : a ≤ 1 / 10) (hay : delta / (2 * tau) + |q0| * a ≤ 1 / 10) :
    SymmetricPerturbation := by
  let f : SupportedTensor := ⟨pulseTensor q0 a N delta tau,
    pulseTensor_contDiff q0 a N delta tau, by
      intro p hp
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => hp (pulseOriginalBox_subset_patchBox hax hay
        (pulseTensor_tsupport_subset ha hd ht N h))⟩
  exact ⟨f, pulseTensor_symmetric q0 a N delta tau⟩

end SmoothLocal.Pulse

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

theorem supportedPulse_seminorm_le (q0 a : ℝ) (ha : 0 < a) (N : ℕ) (delta : ℝ)
    (hd : 0 < delta) {tau : ℝ} (ht : 1 ≤ tau)
    (hax : a ≤ 1 / 10) (hay : delta / (2 * tau) + |q0| * a ≤ 1 / 10) (k : ℕ) :
    perturbationSeminorm k
        (supportedPulse q0 a N delta tau ha hd (lt_of_lt_of_le zero_lt_one ht) hax hay) ≤
      pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N := by
  have ht0 : 0 ≤ tau := le_trans zero_le_one ht
  have hC : 0 ≤ pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N :=
    div_nonneg (mul_nonneg (pulseDerivativeBound_nonneg q0 a ha delta k) (pow_nonneg ht0 k))
      (pow_nonneg ht0 N)
  unfold perturbationSeminorm
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ hC k _).mpr
  intro p hp
  exact pulseTensor_derivative_le q0 a ha N delta ht k p

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QMetricDensityDecomposition
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem sixVariableQ_density_split {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) (hxx : stateQDenominator g w ≠ 0) :
    sixVariableQ g w = qMetricFirstLower g w+
      curvatureDensity g (statePoint w)*qMetricDensityFactor g w := by
  have hraw : sixVariableQ g w = stateConnection g 1 1 w+
      ((stateMixed g w)^2+gaussianCurvature g (statePoint w)*stateEnergy g w)/
        stateQDenominator g w := by
    rw [sixVariableQ_explicit hg hU hw]
    rfl
  rw [hraw]
  unfold qMetricFirstLower qMetricDensityFactor curvatureDensity
  have hdet := metricDet_ne_zero hg hw
  field_simp [hdet,hxx]
  ring

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

theorem qFirstDensityFactor_bundle (g : MetricField) (w : DarbouxState) :
    qFirstDensityFactor (qFirstBundle g w) = qMetricDensityFactor g w := rfl
theorem qFirstLower_bundle (g : MetricField) (w : DarbouxState) :
    qFirstLower (qFirstBundle g w) = qMetricFirstLower g w := rfl

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QPrincipal
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem hessian_time_ratio {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    (hessianQuotient g z p) ^ 2 + gaussianCurvature g p * darbouxG g z p =
      covHessian g z p 0 0 / covHessian g z p 1 1 := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  unfold hessianQuotient darbouxG
  field_simp [hyy]
  nlinarith [hdet]

end SmoothLocal.HighEquation

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

theorem covHessian_shear_entries {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U) :
    let H := covHessian g z (inverseShearCoordinates q0 p)
    let S := covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p
    S 1 1 = H 1 1 ∧ S 0 1 = H 0 1 - q0 * H 1 1 ∧
      S 0 0 = H 0 0 - 2 * q0 * H 0 1 + q0 ^ 2 * H 1 1 := by
  dsimp only
  rw [covHessian_in_shear_coordinates hg hz hU q0 hp]
  simp only [inverseShearMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [covHessian_symm hg hU hz hp 1 0]
  constructor
  · ring
  constructor <;> ring

theorem hessianQuotient_in_shear_coordinates {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hyy : covHessian g z (inverseShearCoordinates q0 p) 1 1 ≠ 0) :
    hessianQuotient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p =
      hessianQuotient g z (inverseShearCoordinates q0 p) - q0 := by
  obtain ⟨h11, h01, h00⟩ := covHessian_shear_entries hg hz hU q0 hp
  unfold hessianQuotient
  rw [h01, h11]
  field_simp [hyy]

theorem sheared_Hxx_factor {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hyy : covHessian g z (inverseShearCoordinates q0 p) 1 1 ≠ 0)
    (hD : (covHessian g z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature g (inverseShearCoordinates q0 p) *
        heightEnergy g z (inverseShearCoordinates q0 p)) :
    covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 =
      ((hessianQuotient g z (inverseShearCoordinates q0 p) - q0)^2 +
        gaussianCurvature g (inverseShearCoordinates q0 p) *
          darbouxG g z (inverseShearCoordinates q0 p)) *
            covHessian g z (inverseShearCoordinates q0 p) 1 1 := by
  have hratio := hessian_time_ratio hg hU hz hp hyy hD
  obtain ⟨h11, h01, h00⟩ := covHessian_shear_entries hg hz hU q0 hp
  rw [h00]
  have hf : covHessian g z (inverseShearCoordinates q0 p) 0 0 =
      ((hessianQuotient g z (inverseShearCoordinates q0 p))^2 +
        gaussianCurvature g (inverseShearCoordinates q0 p) *
          darbouxG g z (inverseShearCoordinates q0 p)) *
            covHessian g z (inverseShearCoordinates q0 p) 1 1 := by
    rw [hratio, div_mul_cancel₀ _ hyy]
  rw [hf]
  unfold hessianQuotient
  field_simp [hyy]
  ring

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_ShearMetricJets
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
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

theorem coordinateBound_add_on {f h : Coord → ℝ} {U S : Set Coord}
    {N : ℕ} {A B : ℝ} (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U)
    (hU : IsOpen U) (hSU : S ⊆ U) (hA : CoordinateBound f S N A) (hB : CoordinateBound h S N B) :
    CoordinateBound (fun p => f p + h p) S N (A + B) := by
  intro ds hds p hp
  rw [CoordinateBound.iterated_add hf hh hU ds (hSU hp)]
  exact (abs_add_le _ _).trans (add_le_add (hA ds hds p hp) (hB ds hds p hp))

theorem coordinateBound_const_mul_on {f : Coord → ℝ} {U S : Set Coord}
    {N : ℕ} {A : ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) (hSU : S ⊆ U) (hA : CoordinateBound f S N A) (c : ℝ) :
    CoordinateBound (fun p => c * f p) S N (|c| * A) := by
  intro ds hds p hp
  rw [CoordinateBound.iterated_const_mul hf hU c ds (hSU hp), abs_mul]
  exact mul_le_mul_of_nonneg_left (hA ds hds p hp) (abs_nonneg _)

theorem metric_coordinate_bound_inverse_shear
    {g : MetricField} {U S : Set Coord} {N : ℕ} {G : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : S ⊆ U) (hG : 0 ≤ G)
    (hgB : ∀ i j, CoordinateBound (fun p => g p i j) S N G) (q0 : ℝ) :
    ∀ i j, CoordinateBound (fun p => metricInShearCoordinates g q0 p i j)
      (inverseShearCoordinates q0 ⁻¹' S) N (shearedMetricCoordinateBudget G q0 N) := by
  let V := inverseShearCoordinates q0 ⁻¹' U
  let T := inverseShearCoordinates q0 ⁻¹' S
  let A := (2 * (1 + |q0|))^N * G
  let B := (1 + |q0|)^2 * A
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  have hVU : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hTV : T ⊆ V := fun p hp => hSU hp
  have hs (a b : Fin 2) : ContDiffOn ℝ ∞ (heightInShearCoordinates (fun p => g p a b) q0) V :=
    heightInShearCoordinates_contDiffOn (hg.1 a b) q0
  have hb (a b : Fin 2) :
      CoordinateBound (heightInShearCoordinates (fun p => g p a b) q0) T N A :=
    SmoothLocal.Pulse.CoordinateBound.inverse_shear (hgB a b) (hg.1 a b) hU hSU hG q0
  intro i j
  let term (a b : Fin 2) : Coord → ℝ := fun p =>
    (inverseShearMatrix q0 a i * inverseShearMatrix q0 b j) *
      heightInShearCoordinates (fun r => g r a b) q0 p
  have htS (a b : Fin 2) : ContDiffOn ℝ ∞ (term a b) V := contDiffOn_const.mul (hs a b)
  have htB (a b : Fin 2) : CoordinateBound (term a b) T N B := by
    have hh := coordinateBound_const_mul_on (hs a b) hVU hTV (hb a b)
      (inverseShearMatrix q0 a i * inverseShearMatrix q0 b j)
    apply hh.mono le_rfl
    have hc : |inverseShearMatrix q0 a i * inverseShearMatrix q0 b j| ≤ (1 + |q0|)^2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul (inverseShearMatrix_entry_bound q0 a i) (inverseShearMatrix_entry_bound q0 b j)
        (abs_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right hc hA
  have hrow0 := coordinateBound_add_on (htS 0 0) (htS 0 1) hVU hTV (htB 0 0) (htB 0 1)
  have hrow1 := coordinateBound_add_on (htS 1 0) (htS 1 1) hVU hTV (htB 1 0) (htB 1 1)
  have hsum := coordinateBound_add_on ((htS 0 0).add (htS 0 1))
    ((htS 1 0).add (htS 1 1)) hVU hTV hrow0 hrow1
  rw [metricInShearCoordinates_four_terms]
  have hbudget : B + B + (B + B) = shearedMetricCoordinateBudget G q0 N := by
    dsimp [B, A, shearedMetricCoordinateBudget]
    ring
  rw [hbudget] at hsum
  exact hsum

end SmoothLocal.Pulse

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

theorem movingPrimitive_hasDerivAt
    {f : Coord → ℝ} {x : ℝ → ℝ} {radius lo hi theta dx : ℝ}
    (hf : ContDiffOn ℝ ∞ f (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hx : HasDerivAt x dx theta) (hxt : x theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    HasDerivAt (fun t => coordinatePrimitive f (coordinatePoint (x t) t))
      (dx * f (coordinatePoint (x theta) theta) +
        ∫ xi in 0..x theta, coordPartial 1 f (coordinatePoint xi theta)) theta := by
  have hp := point_mem_rectangle hxt htheta
  have hd : DifferentiableAt ℝ (coordinatePrimitive f) (coordinatePoint (x theta) theta) :=
    ((coordinatePrimitive_contDiffOn hf).contDiffAt
      ((coordinateRectangle_isOpen radius lo hi).mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hchain := HasFDerivAt.comp_hasDerivAt theta
    (f := fun t => coordinatePoint (x t) t) hd.hasFDerivAt
    (movingPoint_hasDerivAt (x := x) hx)
  have ht := coordinatePrimitive_partial_t hf hradius hp
  have hs := coordinatePrimitive_partial_s hf hradius hp
  simp only [coordPartial] at ht hs
  simp only [map_add, map_smul,
    smul_eq_mul, ht, hs] at hchain
  simpa [coordinatePoint, coordPartial, Function.comp_def] using hchain

theorem movingIntervalIntegral_hasDerivAt
    {f : Coord → ℝ} {left right : ℝ → ℝ} {radius lo hi theta dl dr : ℝ}
    (hf : ContDiffOn ℝ ∞ f (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hl : HasDerivAt left dl theta) (hr : HasDerivAt right dr theta)
    (hlt : left theta ∈ Ioo (-radius) radius)
    (hrt : right theta ∈ Ioo (-radius) radius) (htheta : theta ∈ Ioo lo hi) :
    HasDerivAt (movingIntervalIntegral left right f)
      ((∫ xi in left theta..right theta, coordPartial 1 f (coordinatePoint xi theta)) +
        dr * f (coordinatePoint (right theta) theta) -
        dl * f (coordinatePoint (left theta) theta)) theta := by
  have hright := movingPrimitive_hasDerivAt hf hradius hr hrt htheta
  have hleft := movingPrimitive_hasDerivAt hf hradius hl hlt htheta
  have hdiff := hright.sub hleft
  have h0 : (0 : ℝ) ∈ Ioo (-radius) radius := ⟨by linarith, hradius⟩
  have hf1 := (partial_contDiffOn hf (coordinateRectangle_isOpen radius lo hi) 1).continuousOn
  have hIsub := intervalIntegral.integral_interval_sub_left
    (slice_intervalIntegrable hf1 h0 hrt htheta)
    (slice_intervalIntegrable hf1 h0 hlt htheta)
  have he :
      (dr * f (coordinatePoint (right theta) theta) +
        ∫ xi in 0..right theta, coordPartial 1 f (coordinatePoint xi theta)) -
      (dl * f (coordinatePoint (left theta) theta) +
        ∫ xi in 0..left theta, coordPartial 1 f (coordinatePoint xi theta)) =
      (∫ xi in left theta..right theta, coordPartial 1 f (coordinatePoint xi theta)) +
        dr * f (coordinatePoint (right theta) theta) -
        dl * f (coordinatePoint (left theta) theta) := by linarith
  rw [he] at hdiff
  apply hdiff.congr_of_eventuallyEq
  filter_upwards [hl.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hlt),
    hr.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hrt),
    isOpen_Ioo.mem_nhds htheta] with t hlt' hrt' ht'
  exact movingIntervalIntegral_eq_primitive hf.continuousOn hradius hlt' hrt' ht'

theorem inwardIntervalIntegral_hasDerivAt
    {f : Coord → ℝ} {radius lo hi xl xr theta0 speed theta : ℝ}
    (hf : ContDiffOn ℝ ∞ f (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hl : inwardLeft xl theta0 speed theta ∈ Ioo (-radius) radius)
    (hr : inwardRight xr theta0 speed theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi) :
    HasDerivAt
      (movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed) f)
      ((∫ xi in inwardLeft xl theta0 speed theta..inwardRight xr theta0 speed theta,
          coordPartial 1 f (coordinatePoint xi theta)) -
        speed * (f (coordinatePoint (inwardRight xr theta0 speed theta) theta) +
          f (coordinatePoint (inwardLeft xl theta0 speed theta) theta))) theta := by
  convert movingIntervalIntegral_hasDerivAt hf hradius
    (inwardLeft_hasDerivAt xl theta0 speed theta)
    (inwardRight_hasDerivAt xr theta0 speed theta) hl hr htheta using 1
  all_goals try with_reducible_and_instances rfl
  ring

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

theorem movingSourceNorm_continuousOn
    {R : Coord → ℝ} {radius lo hi xl xr a b speed : ℝ}
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi)) (hradius : 0 < radius)
    (hleft : ∀ t ∈ Icc a b, inwardLeft xl a speed t ∈ Ioo (-radius) radius)
    (hright : ∀ t ∈ Icc a b, inwardRight xr a speed t ∈ Ioo (-radius) radius)
    (htime : Icc a b ⊆ Ioo lo hi) :
    ContinuousOn (movingSourceNorm xl xr a speed R) (Icc a b) := by
  intro t ht
  have hd := inwardIntervalIntegral_hasDerivAt (hR.pow 2) hradius
    (hleft t ht) (hright t ht) (htime ht)
  exact hd.continuousAt.sqrt.continuousWithinAt

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MovingSlabEnergy
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

variable {P S bTheta bXi v R : Coord → ℝ} {radius lo hi xl xr theta0 speed theta : ℝ}

theorem movingEnergy_hasDerivAt_of_sliceEquation
    (hP : ContDiffOn ℝ ∞ P (coordinateRectangle radius lo hi))
    (hS : ContDiffOn ℝ ∞ S (coordinateRectangle radius lo hi))
    (hbt : ContDiffOn ℝ ∞ bTheta (coordinateRectangle radius lo hi))
    (hbx : ContDiffOn ℝ ∞ bXi (coordinateRectangle radius lo hi))
    (hv : ContDiffOn ℝ ∞ v (coordinateRectangle radius lo hi))
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi))
    (hradius : 0 < radius)
    (hl : inwardLeft xl theta0 speed theta ∈ Ioo (-radius) radius)
    (hr : inwardRight xr theta0 speed theta ∈ Ioo (-radius) radius)
    (htheta : theta ∈ Ioo lo hi)
    (hEq : ∀ x ∈ uIcc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta),
      hyperbolicOperator P S v (coordinatePoint x theta) =
        bTheta (coordinatePoint x theta) * coordPartial 1 v (coordinatePoint x theta) +
        bXi (coordinatePoint x theta) * coordPartial 0 v (coordinatePoint x theta) +
        R (coordinatePoint x theta)) :
    HasDerivAt (movingEnergy xl xr theta0 speed S v)
      (movingEnergyRate xl xr theta0 speed P S bTheta bXi v R theta) theta := by
  let U := coordinateRectangle radius lo hi
  have hU : IsOpen U := coordinateRectangle_isOpen radius lo hi
  obtain ⟨he, hj, herr⟩ := energy_fields_contDiffOn hU hP hS hbt hbx hv
  have hrest : ContDiffOn ℝ ∞
      (fun p => energyCoefficientError P S bTheta bXi v p + R p * coordPartial 1 v p) U :=
    herr.add (hR.mul (partial_contDiffOn hv hU 1))
  have hmem {x : ℝ}
      (hx : x ∈ uIcc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta)) :
      coordinatePoint x theta ∈ U :=
    point_mem_rectangle
      ⟨lt_of_lt_of_le (lt_min hl.1 hr.1) hx.1,
        lt_of_le_of_lt hx.2 (max_lt hl.2 hr.2)⟩ htheta
  have hlocal (x : ℝ)
      (hx : x ∈ uIcc (inwardLeft xl theta0 speed theta) (inwardRight xr theta0 speed theta)) :
      coordPartial 1 (energyDensity S v) (coordinatePoint x theta) =
        coordPartial 0 (energyFlux P S v) (coordinatePoint x theta) +
          (energyCoefficientError P S bTheta bXi v (coordinatePoint x theta) +
            R (coordinatePoint x theta) * coordPartial 1 v (coordinatePoint x theta)) := by
    have hp := hmem hx
    have hh := energy_density_flux_identity
      ((hP.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      ((hS.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hv hU hp (hEq x hx)
    linarith
  have hint :
      (∫ x in inwardLeft xl theta0 speed theta..inwardRight xr theta0 speed theta,
        coordPartial 1 (energyDensity S v) (coordinatePoint x theta)) =
      energyFlux P S v (coordinatePoint (inwardRight xr theta0 speed theta) theta) -
        energyFlux P S v (coordinatePoint (inwardLeft xl theta0 speed theta) theta) +
      movingIntervalIntegral (inwardLeft xl theta0 speed) (inwardRight xr theta0 speed)
        (fun p => energyCoefficientError P S bTheta bXi v p + R p * coordPartial 1 v p) theta := by
    calc
      _ = ∫ x in inwardLeft xl theta0 speed theta..inwardRight xr theta0 speed theta,
          coordPartial 0 (energyFlux P S v) (coordinatePoint x theta) +
            (energyCoefficientError P S bTheta bXi v (coordinatePoint x theta) +
              R (coordinatePoint x theta) * coordPartial 1 v (coordinatePoint x theta)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hlocal x hx
      _ = _ := by
        rw [intervalIntegral.integral_add
          (slice_intervalIntegrable (partial_contDiffOn hj hU 0).continuousOn hl hr htheta)
          (slice_intervalIntegrable hrest.continuousOn hl hr htheta),
          slice_integral_partial_xi hj hl hr htheta]
        rfl
  have hd := inwardIntervalIntegral_hasDerivAt he hradius hl hr htheta
  rw [hint] at hd
  refine hd.congr_deriv (Eq.symm ?_)
  · dsimp only [movingEnergyRate]
    ring

theorem moving_slab_energy_propagation
    {P S bTheta bXi v R : Coord → ℝ} {radius lo hi xl xr a b speed s0 M : ℝ}
    (hP : ContDiffOn ℝ ∞ P (coordinateRectangle radius lo hi))
    (hS : ContDiffOn ℝ ∞ S (coordinateRectangle radius lo hi))
    (hbt : ContDiffOn ℝ ∞ bTheta (coordinateRectangle radius lo hi))
    (hbx : ContDiffOn ℝ ∞ bXi (coordinateRectangle radius lo hi))
    (hv : ContDiffOn ℝ ∞ v (coordinateRectangle radius lo hi))
    (hR : ContDiffOn ℝ ∞ R (coordinateRectangle radius lo hi))
    (hradius : 0 < radius) (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hxl : -radius < xl) (hxr : xr < radius)
    (ha : a ∈ Ioo lo hi) (hb : b ∈ Ioo lo hi)
    (hlength : 2 * speed * (b - a) < xr - xl)
    (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hSfloor : ∀ p ∈ shrinkingSlab xl xr a b speed, s0 ≤ S p)
    (hcoeff : ∀ p ∈ shrinkingSlab xl xr a b speed,
      |bTheta p| ≤ M ∧ |bXi p| ≤ M ∧ |coordPartial 0 P p| ≤ M ∧
        |coordPartial 0 S p| ≤ M ∧ |coordPartial 1 S p| ≤ M)
    (hchar : ∀ p ∈ shrinkingSlab xl xr a b speed, |P p| + Real.sqrt (S p) ≤ speed)
    (hEq : ∀ p ∈ shrinkingSlab xl xr a b speed, hyperbolicOperator P S v p =
      bTheta p * coordPartial 1 v p + bXi p * coordPartial 0 v p + R p) :
    Real.sqrt (movingEnergy xl xr a speed S v b) ≤
      Real.exp ((8 * M * (1 + 1 / s0)) * (b - a)) *
        (Real.sqrt (∫ xi in xl..xr, energyDensity S v (coordinatePoint xi a)) +
          ∫ t in a..b, movingSourceNorm xl xr a speed R t) := by
  have htime : Icc a b ⊆ Ioo lo hi :=
    fun t ht => ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
  have hgeo (t : ℝ) (ht : t ∈ Icc a b) :=
    inward_interval_geometry hab hspeed hxl hxr hlength ht
  have hleft (t : ℝ) (ht : t ∈ Icc a b) := (hgeo t ht).1
  have hright (t : ℝ) (ht : t ∈ Icc a b) := (hgeo t ht).2.1
  have horder (t : ℝ) (ht : t ∈ Icc a b) := (hgeo t ht).2.2.1.le
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (movingEnergy xl xr a speed S v)
        (movingEnergyRate xl xr a speed P S bTheta bXi v R t) t := by
    apply movingEnergy_hasDerivAt_of_sliceEquation hP hS hbt hbx hv hR hradius
      (hleft t ht) (hright t ht) (htime ht)
    intro x hx
    rw [uIcc_of_le (horder t ht)] at hx
    exact hEq _ (point_mem_shrinkingSlab ht hx)
  have hEcont : ContinuousOn (movingEnergy xl xr a speed S v) (Icc a b) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hEpos (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ movingEnergy xl xr a speed S v t := by
    apply movingEnergy_nonneg (horder t ht)
    intro x hx
    exact hs0.le.trans (hSfloor _ (point_mem_shrinkingSlab ht hx))
  have hforce := movingSourceNorm_continuousOn hR hradius hleft hright htime
  have hC : 0 ≤ 8 * M * (1 + 1 / s0) := by positivity
  have hbound (t : ℝ) (ht : t ∈ Ioo a b) :
      movingEnergyRate xl xr a speed P S bTheta bXi v R t ≤
        (8 * M * (1 + 1 / s0)) * movingEnergy xl xr a speed S v t +
          Real.sqrt (2 * movingEnergy xl xr a speed S v t) * movingSourceNorm xl xr a speed R t := by
    apply movingEnergyRate_le_of_sliceBounds hP hS hbt hbx hv hR
      (hleft t ⟨ht.1.le, ht.2.le⟩) (hright t ⟨ht.1.le, ht.2.le⟩)
      (htime ⟨ht.1.le, ht.2.le⟩) (horder t ⟨ht.1.le, ht.2.le⟩) hs0 hM
    · intro x hx
      exact hSfloor _ (point_mem_shrinkingSlab ⟨ht.1.le, ht.2.le⟩ hx)
    · intro x hx
      exact hcoeff _ (point_mem_shrinkingSlab ⟨ht.1.le, ht.2.le⟩ hx)
    · intro x hx
      exact hchar _ (point_mem_shrinkingSlab ⟨ht.1.le, ht.2.le⟩ hx)
  have hfinal := sqrt_energy_gronwall hab hEcont
    (fun t ht => hderiv t ⟨ht.1.le, ht.2.le⟩) hEpos hforce
    (fun t _ => Real.sqrt_nonneg _) hC hbound
  simpa only [movingEnergy, movingIntervalIntegral, inwardLeft, inwardRight,
    sub_self, mul_zero, add_zero, sub_zero] using hfinal

end SmoothLocal.Hyperbolic

end

end OAI
end

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

theorem qFixedTimeDomain_isOpen {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (theta : ℝ) :
    IsOpen (qFixedTimeDomain g U theta) :=
  (darbouxQStateDomain_isOpen hg hU).preimage (qFixedTimeState_contDiff theta).continuous

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

theorem sixVariableQ_eq_universalMetricQ {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    sixVariableQ g w = universalMetricQ (metricPBundle g w) := by
  rw [sixVariableQ_explicit hg hU hw]
  have hK := gaussianCurvature_eq_curvatureJet hg hU hw
  unfold solvedDarbouxQ jetNumerator jetMixed jetXX universalMetricQ
  rw [universalConnection_metricPBundle, universalConnection_metricPBundle,
    universalQDenominator_metricPBundle, universalEnergy_metricPBundle]
  simp only [stateConnection, stateQDenominator, stateEnergy, jetXX, metricPBundle, hK]

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

theorem metricQSpatialBundle_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (theta : ℝ) :
    ContDiffOn ℝ ∞ (metricQSpatialBundle g theta) (qFixedTimeBaseDomain U theta) := by
  apply (metricPBundle_contDiffOn hg hU).comp (qFixedTimeState_contDiff theta).contDiffOn
  intro v hv
  change statePoint (qFixedTimeState theta v) ∈ U
  simpa only [statePoint_qFixedTimeState, qFixedTimeBaseDomain, Set.mem_ofPred_eq] using hv

theorem metricQSpatialBundle_positive_jet_bound
    {g : MetricField} {U : Set Coord} {theta G : ℝ} {v : QSpatialState} {N : ℕ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : coordinatePoint (v 0) theta ∈ U)
    (hG : 0 ≤ G) (hgB : HorizontalMetricTwoJetBound g (coordinatePoint (v 0) theta) N G)
    {n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖iteratedFDeriv ℝ n (metricQSpatialBundle g theta) v‖ ≤ max 1 G := by
  have hB := (metricQSpatialBundle_contDiffOn hg hU theta).contDiffAt
    ((qFixedTimeBaseDomain_isOpen hU theta).mem_nhds hp)
  have h0 := hB.fst
  have h1 := hB.snd.fst
  have h2 := hB.snd.snd.fst
  have hId := hB.snd.snd.snd
  change ContDiffAt ℝ ∞ (fun w : QSpatialState => (metricQSpatialBundle g theta w).1) v at h0
  change ContDiffAt ℝ ∞ (fun w : QSpatialState => (metricQSpatialBundle g theta w).2.1) v at h1
  change ContDiffAt ℝ ∞ (fun w : QSpatialState => (metricQSpatialBundle g theta w).2.2.1) v at h2
  have he0 : (fun w : QSpatialState => (metricQSpatialBundle g theta w).1) =
      (fun w => g (coordinatePoint (w 0) theta)) := by
    funext w
    exact congrArg g (statePoint_qFixedTimeState theta w)
  have he1 : (fun w : QSpatialState => (metricQSpatialBundle g theta w).2.1) =
      (fun w d i j => coordPartial d (fun p => g p i j) (coordinatePoint (w 0) theta)) := by
    funext w d i j
    exact congrArg (coordPartial d (fun p => g p i j)) (statePoint_qFixedTimeState theta w)
  have he2 : (fun w : QSpatialState => (metricQSpatialBundle g theta w).2.2.1) =
      (fun w d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (coordinatePoint (w 0) theta)) := by
    funext w d e i j
    exact congrArg (coordPartial d (coordPartial e (fun p => g p i j))) (statePoint_qFixedTimeState theta w)
  rw [he0] at h0
  rw [he1] at h1
  rw [he2] at h2
  have hb0 : ‖iteratedFDeriv ℝ n (fun w : QSpatialState => g (coordinatePoint (w 0) theta)) v‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le h0 n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h0) i) n hG
    intro j
    exact (norm_iteratedFDeriv_fixedTime_coordinate (hg.1 i j) hU hp n).trans (hgB.1 i j n hnN)
  have hb1 : ‖iteratedFDeriv ℝ n
      (fun w : QSpatialState => fun d i j => coordPartial d (fun p => g p i j) (coordinatePoint (w 0) theta)) v‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le (F := Matrix (Fin 2) (Fin 2) ℝ) h1 n hG
    intro d
    have h1d := (contDiffAt_pi (F' := fun _ : Fin 2 => Matrix (Fin 2) (Fin 2) ℝ)).mp h1 d
    apply norm_iteratedFDeriv_pi_le h1d n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h1d) i) n hG
    intro j
    exact (norm_iteratedFDeriv_fixedTime_coordinate (partial_contDiffOn (hg.1 i j) hU d) hU hp n).trans
      (hgB.2.1 d i j n hnN)
  have hb2 : ‖iteratedFDeriv ℝ n
      (fun w : QSpatialState => fun d e i j => coordPartial d (coordPartial e (fun p => g p i j))
        (coordinatePoint (w 0) theta)) v‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le (F := Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) h2 n hG
    intro d
    have h2d := (contDiffAt_pi (F' := fun _ : Fin 2 => Fin 2 → Matrix (Fin 2) (Fin 2) ℝ)).mp h2 d
    apply norm_iteratedFDeriv_pi_le (F := Matrix (Fin 2) (Fin 2) ℝ) h2d n hG
    intro e
    have h2de := (contDiffAt_pi (F' := fun _ : Fin 2 => Matrix (Fin 2) (Fin 2) ℝ)).mp h2d e
    apply norm_iteratedFDeriv_pi_le h2de n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h2de) i) n hG
    intro j
    exact (norm_iteratedFDeriv_fixedTime_coordinate
      (partial_contDiffOn (partial_contDiffOn (hg.1 i j) hU e) hU d) hU hp n).trans
        (hgB.2.2 d e i j n hnN)
  have hb0' : ‖iteratedFDeriv ℝ n (fun w => (metricQSpatialBundle g theta w).1) v‖ ≤ G := by
    rw [he0]
    exact hb0
  have hb1' : ‖iteratedFDeriv ℝ n (fun w => (metricQSpatialBundle g theta w).2.1) v‖ ≤ G := by
    rw [he1]
    exact hb1
  have hb2' : ‖iteratedFDeriv ℝ n (fun w => (metricQSpatialBundle g theta w).2.2.1) v‖ ≤ G := by
    rw [he2]
    exact hb2
  exact norm_iteratedFDeriv_prod_le hB.fst hB.snd n (hb0'.trans (le_max_right _ _))
    (norm_iteratedFDeriv_prod_le hB.snd.fst hB.snd.snd n (hb1'.trans (le_max_right _ _))
      (norm_iteratedFDeriv_prod_le hB.snd.snd.fst hId n (hb2'.trans (le_max_right _ _))
        ((qFixedTimeState_positive_jet_bound theta v hn).trans (le_max_left _ _))))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_ActualRemainderL2
attribute [-instance] _root_.OAI.SmoothLocal.Geometry.instCountablePatchAddress
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

variable {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}

theorem firstJetPairRemainder_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} {Cfirst : ℝ} (hCfirst : 0 ≤ Cfirst) {H : ℝ≥0}
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hfirst : ∀ i : Fin 2, ∀ p ∈ V, |coordPartial 1 (heightPFirst g z i) p| ≤ Cfirst) :
    eLpNorm (firstJetPairRemainder g z (m + 2)) 2 (volume.restrict V) ≤
      firstJetPairL2Budget Cfirst H := by
  have h0 : eLpNorm (heightStateFactor z (m + 2) 0) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) :=
    hheight (m + 2) 0 (by norm_num [heightStateBaseOrder])
  have h1 : eLpNorm (heightStateFactor z (m + 2) 1) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) :=
    hheight (m + 2) 1 (by norm_num [heightStateBaseOrder])
  have hm (i : Fin 2) : AEStronglyMeasurable
      (fun p => coordPartial 1 (heightPFirst g z i) p * coordPartial i (verticalJet z (m + 2)) p)
      (volume.restrict V) :=
    (((partial_contDiffOn (heightPFirst_contDiffOn hg hU hz hyy i) hU 1).continuousOn.mul
      (partial_contDiffOn (verticalJet_contDiffOn hU hz (m + 2)) hU i).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hb0 := (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
    (f := heightStateFactor z (m + 2) 0) hV hCfirst (hfirst 0) (hm 0)).trans
    (mul_le_mul' le_rfl h0)
  have hb1 := (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
    (f := heightStateFactor z (m + 2) 1) hV hCfirst (hfirst 1) (hm 1)).trans
    (mul_le_mul' le_rfl h1)
  exact (eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
    (add_le_add hb0 hb1)

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

theorem metricPBundle_mem_universalQTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {G W d c : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|)
    (hden : c ≤ |stateQDenominator g w|) :
    metricPBundle g w ∈ universalMetricQTube (max G W) d c := by
  refine ⟨⟨?_, hdet⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using
      metricPBundle_norm_bound hg hU hw hG hgB hwB
  · simpa only [Set.mem_preimage, Set.mem_ofPred_eq, universalQDenominator_metricPBundle] using hden

theorem actualQ_jet_bound_from_universalTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) {N : ℕ} {G W d c C : ℝ}
    (hG : 0 ≤ G) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j k, k ≤ N + 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|)
    (hden : c ≤ |stateQDenominator g w|)
    (hC : ∀ k ≤ N, ∀ a ∈ universalMetricQTube (max G W) d c,
      ‖iteratedFDeriv ℝ k universalMetricQ a‖ ≤ C)
    {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (sixVariableQ g) w‖ ≤ n.factorial * C * (max 1 G)^n := by
  have hD := darbouxQStateDomain_isOpen hg hU
  have hsub : darbouxQStateDomain g U ⊆ stateBaseDomain U := fun _ hv => hv.1
  have hf := (metricPBundle_contDiffOn hg hU).mono hsub
  have hmap := metricPBundle_mapsTo_Q_domain hg
  have hmem := metricPBundle_mem_universalQTube hg hU hw.1 hG
    (fun i j k hk => hgB i j k (by omega)) hwB hdet hden
  have ho : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i universalMetricQ universalMetricQDomain (metricPBundle g w)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i universalMetricQDomain_isOpen
      (universalMetricQTube_subset_domain (max G W) hd hc hmem)]
    exact hC i (hi.trans hn) (metricPBundle g w) hmem
  have hi : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (metricPBundle g) (darbouxQStateDomain g U) w‖ ≤ (max 1 G)^i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hD hw]
    exact (metricPBundle_positive_jet_bound hg hU hw.1 hG hgB hi (hin.trans hn)).trans
      (le_self_pow₀ (le_max_left _ _) (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le universalMetricQ_contDiffOn hf
    (WithTop.coe_le_coe.mpr le_top) universalMetricQDomain_isOpen.uniqueDiffOn hD.uniqueDiffOn
    hmap hw ho hi
  have heq : iteratedFDerivWithin ℝ n (sixVariableQ g) (darbouxQStateDomain g U) w =
      iteratedFDerivWithin ℝ n (universalMetricQ ∘ metricPBundle g) (darbouxQStateDomain g U) w :=
    iteratedFDerivWithin_congr (fun _ hv => sixVariableQ_eq_universalMetricQ hg hU hv.1) hw n
  rw [iteratedFDerivWithin_of_isOpen n hD hw] at heq
  rw [← heq] at hcomp
  exact hcomp

theorem exists_local_metric_Q_jet_bound (G W : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ∀ w : DarbouxState,
      statePoint w ∈ U →
      (∀ i j k, k ≤ N + 2 →
        ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G) →
      ‖w‖ ≤ W → d ≤ |(g (statePoint w)).det| → c ≤ |stateQDenominator g w| →
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n (sixVariableQ g) w‖ ≤ C := by
  classical
  obtain ⟨C0, hC0, hCP⟩ := universalMetricQTube_finite_bounds (max G W) hd hc N
  let C : ℝ := ∑ k : Fin (N + 1), (k.val.factorial : ℝ) * C0 * (max 1 G)^k.val
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => by positivity)
  refine ⟨C, hC, ?_⟩
  intro g U hg hU w hw hgB hwB hdet hden n hn
  have hne : stateQDenominator g w ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hden
    linarith
  have hb := actualQ_jet_bound_from_universalTube hg hU ⟨hw, hne⟩ hG hd hc hgB hwB hdet hden hCP hn
  let j : Fin (N + 1) := ⟨n, by omega⟩
  have hsum : (j.val.factorial : ℝ) * C0 * (max 1 G)^j.val ≤
      ∑ i : Fin (N+1), (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val :=
    Finset.single_le_sum
      (f := fun i : Fin (N+1) => (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val)
      (fun _ _ => by positivity) (Finset.mem_univ j)
  exact hb.trans hsum

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_BoundedHeightClasses
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.HighEquation

theorem PatchAdmissibleHeight.exists_integer_bound {g : MetricField} {z : Coord → ℝ}
    (h : PatchAdmissibleHeight g z) : ∃ M : ℕ, BoundedAdmissibleHeight g M z := by
  have horiginal := h
  obtain ⟨U, hU, hSU, hg, hz, _, hE, hyy, _⟩ := h
  obtain ⟨Z, _, hzB⟩ := compact_finite_fullJet_bound hz hU modelSquare_isCompact hSU 8
  have hHcont : ContinuousOn (fun p => covHessian g z p 1 1) modelSquare :=
    (covHessian_contDiffOn hg hU hz 1 1).continuousOn.mono hSU
  obtain ⟨H, hH⟩ := modelSquare_isCompact.exists_bound_of_continuousOn hHcont
  obtain ⟨c, hc, hcfloor⟩ := modelSquare_isCompact.exists_forall_le'
    hHcont.abs (fun p hp => abs_pos.mpr (hyy p hp))
  obtain ⟨e, he, hefloor⟩ := modelSquare_isCompact.exists_forall_le'
    ((heightEnergy_contDiffOn hg hU hz).continuousOn.mono hSU) hE
  let B := max 1 (max Z (max H (max (1 / c) (1 / e))))
  obtain ⟨M, hM⟩ := exists_nat_ge B
  have hMone : (1 : ℝ) ≤ (M : ℝ) := (le_max_left _ _).trans hM
  have hMposR : (0 : ℝ) < (M : ℝ) := zero_lt_one.trans_le hMone
  have hMpos : 0 < M := Nat.cast_pos.mp hMposR
  have hZM : Z ≤ (M : ℝ) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hM
  have hHM : H ≤ (M : ℝ) :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hM
  have hcM : 1 / c ≤ (M : ℝ) :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))).trans hM
  have heM : 1 / e ≤ (M : ℝ) :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))).trans hM
  have hMc : 1 / (M : ℝ) ≤ c := (one_div_le hMposR hc).mpr hcM
  have hMe : 1 / (M : ℝ) ≤ e := (one_div_le hMposR he).mpr heM
  refine ⟨M, hMpos, horiginal, ?_, ?_, ?_⟩
  · intro k hk p hp
    exact (hzB k hk p hp).trans hZM
  · intro p hp
    refine ⟨hMc.trans (hcfloor p hp), ?_⟩
    have hh : |covHessian g z p 1 1| ≤ H := by
      simpa only [Real.norm_eq_abs] using hH p hp
    exact hh.trans hHM
  · intro p hp
    exact hMe.trans (hefloor p hp)

end SmoothLocal.Geometry

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

def boundedHeightClass (g0 : MetricField) (kappa : ℝ) (M : ℕ) (q0 : ℚ) :
    Set (metricPatchSet g0 kappa) :=
  {eta | ∃ z : Coord → ℝ, BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z ∧
    |hessianQuotient (perturbedMetric g0 eta.val) z 0 - (q0 : ℝ)| <
      1 / (100 * boundedClassWidth kappa M)}

theorem boundedHeightClass_label_abs_lt {g0 : MetricField} {kappa : ℝ} {M : ℕ} {q0 : ℚ}
    (hne : (boundedHeightClass g0 kappa M q0).Nonempty) : |(q0 : ℝ)| < 1 / 20 := by
  obtain ⟨eta, z, hz, hlabel⟩ := hne
  obtain ⟨_, _, _, _, _, _, _, _, hq⟩ := hz.2.1
  have hzero : (0 : Coord) ∈ SmoothLocal.Flow.modelSquare := by
    constructor <;> intro _ <;> norm_num
  have hqzero := hq 0 hzero
  have hL := boundedClassWidth_ge_hundred kappa M
  have hden : (100 : ℝ) < 100 * boundedClassWidth kappa M := by linarith
  have htolerance : 1 / (100 * boundedClassWidth kappa M) < (1 : ℝ) / 100 :=
    one_div_lt_one_div_of_lt (by norm_num) hden
  have htriangle : |(q0 : ℝ)| ≤
      |(q0 : ℝ) - hessianQuotient (perturbedMetric g0 eta.val) z 0| +
        |hessianQuotient (perturbedMetric g0 eta.val) z 0| := by
    simpa only [sub_add_cancel] using
      abs_add_le ((q0 : ℝ) - hessianQuotient (perturbedMetric g0 eta.val) z 0)
        (hessianQuotient (perturbedMetric g0 eta.val) z 0)
  rw [abs_sub_comm] at htriangle
  linarith

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QPositiveFloor
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix BigOperators

namespace SmoothLocal.Geometry

theorem covHessian_value_bound {g : MetricField} {z : Coord → ℝ} {p : Coord} {G Z d : ℝ}
    (hG : 0 ≤ G) (_hZ : 0 ≤ Z) (hd : 0 < d)
    (hg0 : ∀ i j, |g p i j| ≤ G)
    (hg1 : ∀ a i j, |coordPartial a (fun q => g q i j) p| ≤ G)
    (hz1 : ∀ i, |coordPartial i z p| ≤ Z)
    (hz2 : ∀ i j, |coordPartial i (coordPartial j z) p| ≤ Z)
    (hdet : d ≤ |(g p).det|) (i j : Fin 2) :
    |covHessian g z p i j| ≤ pointHessianBound G Z d := by
  have hprod (k : Fin 2) : |christoffel g k i j p * coordPartial k z p| ≤
      (3 * (G / d) * G) * Z := by
    rw [abs_mul]
    exact mul_le_mul (christoffel_value_bound hG hd hg0 hg1 hdet k i j) (hz1 k)
      (abs_nonneg _) (by positivity)
  unfold covHessian
  rw [Fin.sum_univ_two]
  calc
    _ ≤ |coordPartial i (coordPartial j z) p| +
        |christoffel g 0 i j p * coordPartial 0 z p +
          christoffel g 1 i j p * coordPartial 1 z p| := abs_sub _ _
    _ ≤ Z + (|christoffel g 0 i j p * coordPartial 0 z p| +
        |christoffel g 1 i j p * coordPartial 1 z p|) :=
      add_le_add (hz2 i j) (abs_add_le _ _)
    _ ≤ Z + ((3 * (G / d) * G) * Z + (3 * (G / d) * G) * Z) :=
      add_le_add le_rfl (add_le_add (hprod 0) (hprod 1))
    _ = pointHessianBound G Z d := by unfold pointHessianBound; ring

end SmoothLocal.Geometry

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Flow

theorem sheared_Hxx_value_bound
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord} {G Z d : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (q0 : ℝ) (hp : inverseShearCoordinates q0 p ∈ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d)
    (hg0 : ∀ i j, |g (inverseShearCoordinates q0 p) i j| ≤ G)
    (hg1 : ∀ a i j, |coordPartial a (fun q => g q i j) (inverseShearCoordinates q0 p)| ≤ G)
    (hz1 : ∀ i, |coordPartial i z (inverseShearCoordinates q0 p)| ≤ Z)
    (hz2 : ∀ i j, |coordPartial i (coordPartial j z) (inverseShearCoordinates q0 p)| ≤ Z)
    (hdet : d ≤ |(g (inverseShearCoordinates q0 p)).det|) :
    |covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0| ≤
      shearedHessianUpper G Z d q0 := by
  let H := pointHessianBound G Z d
  have hHN : 0 ≤ H := pointHessianBound_nonneg hG hZ hd
  have hH (i j : Fin 2) := covHessian_value_bound hG hZ hd hg0 hg1 hz1 hz2 hdet i j
  have he := (covHessian_shear_entries hg hz hU q0 hp).2.2
  rw [he]
  have hq : |q0^2| = |q0|^2 := abs_pow q0 2
  calc
    _ ≤ |covHessian g z (inverseShearCoordinates q0 p) 0 0 -
        2 * q0 * covHessian g z (inverseShearCoordinates q0 p) 0 1| +
        |q0^2 * covHessian g z (inverseShearCoordinates q0 p) 1 1| := abs_add_le _ _
    _ ≤ (|covHessian g z (inverseShearCoordinates q0 p) 0 0| +
        |2 * q0 * covHessian g z (inverseShearCoordinates q0 p) 0 1|) +
        |q0^2 * covHessian g z (inverseShearCoordinates q0 p) 1 1| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ H + 2 * |q0| * H + |q0|^2 * H := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), hq]
      exact add_le_add (add_le_add (hH 0 0)
        (mul_le_mul_of_nonneg_left (hH 0 1) (by positivity)))
        (mul_le_mul_of_nonneg_left (hH 1 1) (sq_nonneg _))
    _ ≤ shearedHessianUpper G Z d q0 := by
      change H + 2 * |q0| * H + |q0|^2 * H ≤ 1 + (1 + |q0|)^2 * H
      nlinarith

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricPatchOpen
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem perturbationTensor_isHermitian (η : SymmetricPerturbation) (p : Coord) :
    (perturbationTensor η p).IsHermitian := by
  change (perturbationTensor η p)ᴴ = perturbationTensor η p
  ext i j
  simpa only [Matrix.conjTranspose_apply, star_trivial] using
    perturbationTensor_symmetric η p j i

theorem perturbedMetric_isHermitian {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (η : SymmetricPerturbation)
    {p : Coord} (hp : p ∈ U) : (perturbedMetric g0 η p).IsHermitian :=
  (hg0.2 p hp).isHermitian.add (perturbationTensor_isHermitian η p)

def metricPositiveSet (g0 : MetricField) : Set SymmetricPerturbation :=
  {η | ∀ p ∈ modelSquare, (perturbedMetric g0 η p).PosDef}

theorem metricPositiveSet_mem_nhds {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {η : SymmetricPerturbation} (hη : η ∈ metricPositiveSet g0) :
    metricPositiveSet g0 ∈ 𝓝 η := by
  have hcompact : IsCompact (modelSquare ×ˢ Metric.sphere (0 : Coord) 1) :=
    modelSquare_isCompact.prod (isCompact_sphere (0 : Coord) 1)
  have hgood : ∀ᶠ θ in 𝓝 η, ∀ pv ∈ modelSquare ×ˢ Metric.sphere (0 : Coord) 1,
      0 < metricQuadraticValue (perturbedMetric g0 θ pv.1) pv.2 := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro pv hpv
    have hm : Continuous (fun a : SymmetricPerturbation × (Coord × Coord) => (a.1, a.2.1)) :=
      continuous_fst.prodMk (continuous_fst.comp continuous_snd)
    have hcoeff (i j : Fin 2) : ContinuousAt
        (fun a : SymmetricPerturbation × (Coord × Coord) => perturbedMetric g0 a.1 a.2.1 i j)
        (η, pv) := by
      have hb : ContinuousAt
          (fun a : SymmetricPerturbation × Coord => perturbedMetric g0 a.1 a.2 i j) (η, pv.1) :=
        perturbedMetric_coeff_joint_continuousAt (η := η) hg0 hU (hSU hpv.1) i j
      have hh := hb.comp (x := (η, pv)) hm.continuousAt
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      rfl
    have hv (i : Fin 2) : ContinuousAt
        (fun a : SymmetricPerturbation × (Coord × Coord) => a.2.2 i) (η, pv) := by fun_prop
    have hc := metricQuadraticValue_continuousAt hcoeff hv
    have hvne : pv.2 ≠ 0 := by
      intro hz
      have hn : ‖pv.2‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hpv.2
      simp only [hz, norm_zero] at hn
      norm_num at hn
    have hq : 0 < metricQuadraticValue (perturbedMetric g0 η pv.1) pv.2 := by
      simpa only [metricQuadraticValue, star_trivial] using (hη pv.1 hpv.1).dotProduct_mulVec_pos hvne
    exact continuousAt_const.eventually_lt hc hq
  filter_upwards [hgood] with θ hθ
  intro p hp
  exact posDef_of_positive_on_sphere (perturbedMetric_isHermitian hg0 θ (hSU hp))
    (fun v hv => hθ (p, v) ⟨hp, hv⟩)

theorem centralCurvatureJet_eventually {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {kappa : ℝ} {η : SymmetricPerturbation}
    (hpos : η ∈ metricPositiveSet g0)
    (hK : ∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 η) p < -kappa / 2) :
    ∀ᶠ θ in 𝓝 η, ∀ p ∈ centralBox, perturbedCurvatureJet g0 θ p < -kappa / 2 := by
  have hc : IsCompact centralBox := isCompact_Icc
  apply hc.eventually_forall_of_forall_eventually
  intro p hp
  have hpU := hSU (centralBox_subset_modelSquare hp)
  have hpd : (perturbedMetric g0 η p).PosDef := hpos p (centralBox_subset_modelSquare hp)
  have hd : (perturbedMetric g0 η p).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit).ne_zero
  have hcont := perturbedCurvatureJet_joint_continuousAt hg0 hU hpU hd
  have hval : perturbedCurvatureJet g0 η p < -kappa / 2 := by
    rw [← gaussianCurvature_perturbedMetric_eq_jet hg0 hU η hpos hpU]
    exact hK p hp
  exact hcont.eventually_lt continuousAt_const hval

theorem metricPatchSet_isOpen {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) (kappa : ℝ) :
    IsOpen (metricPatchSet g0 kappa) := by
  apply isOpen_iff_mem_nhds.mpr
  intro η hη
  have hpos : η ∈ metricPositiveSet g0 := hη.1
  filter_upwards [metricPositiveSet_mem_nhds hg0 hU hSU hpos,
    centralCurvatureJet_eventually hg0 hU hSU hpos hη.2] with θ hθpos hθK
  refine ⟨hθpos, ?_⟩
  intro p hp
  rw [gaussianCurvature_perturbedMetric_eq_jet hg0 hU θ hθpos
    (hSU (centralBox_subset_modelSquare hp))]
  exact hθK p hp

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_BoundedPatchSlabGeometry
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
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

theorem actual_patch_curvature_on_class_slab {g0 : MetricField} {kappa q0 r b : ℝ} {M : ℕ}
    (eta : metricPatchSet g0 kappa) (hr : 0 ≤ r) (hb : b ≤ 0)
    (hLr : boundedClassWidth kappa M * r ≤ 1 / 20) (hq0 : |q0| ≤ 1 / 20)
    {p : Coord}
    (hp : p ∈ shrinkingSlab (-(boundedClassWidth kappa M * r)) (boundedClassWidth kappa M * r)
      (-r) b (boundedClassWidth kappa M / 4)) :
    inverseShearCoordinates q0 p ∈ centralBox ∧
    gaussianCurvature (perturbedMetric g0 eta.val) (inverseShearCoordinates q0 p) < -kappa / 2 := by
  obtain ⟨hx, hy⟩ := shrinking_class_slab_axis_bounds hr hb hp
  have hc := inverseShear_slab_mem_centralBox
    ((by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M)) hr hLr hq0 hx hy
  exact ⟨hc, eta.property.2 _ hc⟩

end SmoothLocal.Perturbation

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

theorem universalQCurvature_metricPBundle {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    universalQCurvature (metricPBundle g w) = gaussianCurvature g (statePoint w) :=
  (gaussianCurvature_eq_curvatureJet hg hU hw).symm

theorem universalQNumerator_metricPBundle {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    universalQNumerator (metricPBundle g w) = stateNumerator g w := by
  unfold universalQNumerator
  rw [universalQCurvature_metricPBundle hg hU hw, universalEnergy_metricPBundle,
    universalConnection_metricPBundle]
  rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QMetricJetTransfer
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

theorem metricPBundle_sub_norm_bound {g g0 : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U)
    {w w0 : DarbouxState} (hp : statePoint w = statePoint w0)
    (hw : statePoint w ∈ U) {epsilon : ℝ} (he : 0 ≤ epsilon)
    (hmetric : ∀ i j k, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun p => g0 p i j - g p i j) (statePoint w)‖ ≤ epsilon)
    (hstate : ‖w0 - w‖ ≤ epsilon) :
    ‖metricPBundle g0 w0 - metricPBundle g w‖ ≤ epsilon := by
  have hwords (i j : Fin 2) (ds : List (Fin 2)) (hds : ds.length ≤ 2) :
      |iteratedCoordPartial ds (fun p => g0 p i j) (statePoint w) -
        iteratedCoordPartial ds (fun p => g p i j) (statePoint w)| ≤ epsilon := by
    rw [← CoordinateBound.iterated_sub (hg0.1 i j) (hg.1 i j) hU ds hw]
    exact (norm_iteratedCoordPartial_le_jet ((hg0.1 i j).sub (hg.1 i j)) hU ds hw).trans
      (hmetric i j ds.length hds)
  have h0 : ‖g0 (statePoint w) - g (statePoint w)‖ ≤ epsilon := by
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    exact hwords i j [] (by norm_num)
  have h1 : ‖(fun d i j => coordPartial d (fun p => g0 p i j) (statePoint w)) -
      (fun d i j => coordPartial d (fun p => g p i j) (statePoint w))‖ ≤ epsilon := by
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro d
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    exact hwords i j [d] (by norm_num)
  have h2 : ‖(fun d e i j => coordPartial d (coordPartial e (fun p => g0 p i j)) (statePoint w)) -
      (fun d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))‖ ≤ epsilon := by
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro d
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro e
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    exact hwords i j [d, e] (by norm_num)
  change max ‖g0 (statePoint w0) - g (statePoint w)‖
    (max ‖(fun d i j => coordPartial d (fun p => g0 p i j) (statePoint w0)) -
      (fun d i j => coordPartial d (fun p => g p i j) (statePoint w))‖
      (max ‖(fun d e i j => coordPartial d (coordPartial e (fun p => g0 p i j)) (statePoint w0)) -
        (fun d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))‖
        ‖w0 - w‖)) ≤ epsilon
  rw [← hp]
  exact max_le h0 (max_le h1 (max_le h2 hstate))

theorem metricPBundle_mem_baseTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {G W d : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|) :
    metricPBundle g w ∈ universalMetricBaseTube (max G W) d := by
  refine ⟨?_, hdet⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    metricPBundle_norm_bound hg hU hw hG hgB hwB

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

theorem stateQDenominator_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateQDenominator g) (stateBaseDomain U) :=
  (contDiffOn_apply ℝ ℝ 5 _).sub (stateConnection_contDiffOn hg hU 0 0)

theorem qCompactTube_isCompact {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M c : ℝ) : IsCompact (qCompactTube g S M c) := by
  have hbase := stateBaseCompact_isCompact hS M
  have hc : ContinuousOn (fun w => |stateQDenominator g w|) (stateBaseCompact S M) :=
    (stateQDenominator_contDiffOn hg hU).continuousOn.abs.mono (fun w hw => hSU hw.1)
  have hclosed : IsClosed (qCompactTube g S M c) :=
    hc.preimage_isClosed_of_isClosed hbase.isClosed isClosed_Ici
  exact hbase.of_isClosed_subset hclosed inter_subset_left

theorem qCompactTube_derivative_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) {f : DarbouxState → ℝ}
    (hf : ContDiffOn ℝ ∞ f (darbouxQStateDomain g U)) (k : ℕ) :
    ∃ C : ℝ, ∀ w ∈ qCompactTube g S M c, ‖iteratedFDeriv ℝ k f w‖ ≤ C := by
  have hDo := darbouxQStateDomain_isOpen hg hU
  have hcont : ContinuousOn (iteratedFDeriv ℝ k f) (darbouxQStateDomain g U) := by
    apply (hf.continuousOn_iteratedFDerivWithin (WithTop.coe_le_coe.mpr le_top)
      hDo.uniqueDiffOn).congr
    intro w hw
    exact (iteratedFDerivWithin_eq_iteratedFDeriv hDo.uniqueDiffOn
      ((hf.contDiffAt (hDo.mem_nhds hw)).of_le (WithTop.coe_le_coe.mpr le_top)) hw).symm
  exact (qCompactTube_isCompact hg hU hS hSU M c).exists_bound_of_continuousOn
    (hcont.mono (qCompactTube_subset_domain hSU M hc))

end SmoothLocal.HighEquation

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

theorem stateNumerator_qSolutionJet_eq_product {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) {p : Coord} (hp : p ∈ U)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    stateNumerator g (qSolutionJet z p) = covHessian g z p 0 0 * covHessian g z p 1 1 := by
  have hd : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1)^2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  unfold stateNumerator jetNumerator
  rw [statePoint_qSolutionJet, stateGradient_qSolutionJet]
  change (jetMixed g p (coordPartial 0 (coordPartial 1 z) p)
    (fun i => coordPartial i z p))^2 +
      gaussianCurvature g p * jetEnergy g p (fun i => coordPartial i z p) = _
  rw [jetMixed_at_height, jetEnergy_at_height hg hp z]
  linarith

theorem stateNumerator_negative_of_solution_floors {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) {p : Coord} (hp : p ∈ U)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    {nu c : ℝ} (_hnu : 0 < nu) (hc : 0 < c)
    (hxx : nu ≤ |covHessian g z p 0 0|) (hyy : c ≤ |covHessian g z p 1 1|)
    (htime : (hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p < 0) :
    stateNumerator g (qSolutionJet z p) ≤ -(nu * c) := by
  have hyne : covHessian g z p 1 1 ≠ 0 := abs_pos.mp (hc.trans_le hyy)
  have hratio : covHessian g z p 0 0 / covHessian g z p 1 1 < 0 := by
    rw [← hessian_time_ratio hg hU hz hp hyne hD]
    exact htime
  have heq : covHessian g z p 0 0 * covHessian g z p 1 1 =
      (covHessian g z p 0 0 / covHessian g z p 1 1) * (covHessian g z p 1 1)^2 := by
    field_simp [hyne]
  have hneg : covHessian g z p 0 0 * covHessian g z p 1 1 < 0 := by
    rw [heq]
    exact mul_neg_of_neg_of_pos hratio (sq_pos_of_ne_zero hyne)
  have hprod := mul_le_mul hxx hyy hc.le (abs_nonneg _)
  rw [← abs_mul, abs_of_neg hneg] at hprod
  rw [stateNumerator_qSolutionJet_eq_product hg hU hz hp hD]
  linarith

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

theorem comparisonDomain_isOpen {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) :
    IsOpen (comparisonDomain g U P I) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  exact inter_mem ((spatialStrip_isOpen hI).mem_nhds hp.1)
    (((qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).contDiffAt
      ((spatialStrip_isOpen hI).mem_nhds hp.1)).continuousAt.preimage_mem_nhds
        ((darbouxQStateDomain_isOpen hg hU).mem_nhds hp.2))

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_BoundedClassInitialJet
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
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Flow SmoothLocal.Perturbation

theorem bounded_class_sheared_solution_state_bound
    {g : MetricField} {z : Coord → ℝ} {M : ℕ} (h : BoundedAdmissibleHeight g M z)
    (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ SmoothLocal.Flow.modelSquare)
    (hcoords : |p 0| ≤ 1 ∧ |p 1| ≤ 1) :
    ‖qSolutionJet (heightInShearCoordinates z q0) p‖ ≤ boundedClassShearedStateBudget q0 M := by
  obtain ⟨_, hadm, hjet, _, _⟩ := h
  obtain ⟨U, hU, hSU, _, hz, _, _, _, _⟩ := hadm
  have hzB : CoordinateBound z SmoothLocal.Flow.modelSquare 2 (M : ℝ) := by
    intro ds hds p hp
    exact (norm_iteratedCoordPartial_le_jet hz hU ds (hSU hp)).trans
      (hjet ds.length (by omega) p hp)
  have hshear := SmoothLocal.Pulse.CoordinateBound.inverse_shear hzB hz hU hSU (Nat.cast_nonneg M) q0
  have hstate : ∀ i : Fin 6, |qSolutionJet (heightInShearCoordinates z q0) p i| ≤
      boundedClassShearedStateBudget q0 M := by
    intro i
    fin_cases i
    · exact hcoords.1.trans (le_max_left _ _)
    · exact hcoords.2.trans (le_max_left _ _)
    · exact (hshear [0] (by norm_num) p hp).trans (le_max_right _ _)
    · exact (hshear [1] (by norm_num) p hp).trans (le_max_right _ _)
    · exact (hshear [0, 1] (by norm_num) p hp).trans (le_max_right _ _)
    · exact (hshear [0, 0] (by norm_num) p hp).trans (le_max_right _ _)
  exact (pi_norm_le_iff_of_nonneg (boundedClassShearedStateBudget_pos q0 M).le).mpr hstate

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ClosureMetricApproximation
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise Distributions

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

@[simp] theorem perturbationSeminorm_zero (k : ℕ) :
    perturbationSeminorm k 0 = 0 := map_zero (perturbationSeminormFamily k)

theorem closure_exists_finite_seminorm_approximation
    {T : Type*} [TopologicalSpace T] (f : T → SymmetricPerturbation) (hf : Continuous f)
    {A : Set T} {theta : T} (hclosure : theta ∈ closure A)
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta ∈ A, ∀ k ≤ n, perturbationSeminorm k (f eta - f theta) < epsilon := by
  let O : Set T := {eta | ∀ k : Fin (n + 1),
    perturbationSeminorm k.val (f eta - f theta) < epsilon}
  have hO : IsOpen O := by
    change IsOpen {eta | ∀ k : Fin (n + 1),
      perturbationSeminorm k.val (f eta - f theta) < epsilon}
    simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro k
    exact isOpen_lt ((perturbationSeminorm_continuous k.val).comp
      (hf.sub continuous_const)) continuous_const
  have htheta : theta ∈ O := by
    intro k
    simpa only [sub_self, perturbationSeminorm_zero] using hepsilon
  obtain ⟨eta, hetaO, hetaA⟩ := mem_closure_iff.mp hclosure O hO htheta
  refine ⟨eta, hetaA, ?_⟩
  intro k hk
  exact hetaO ⟨k, by omega⟩

theorem perturbation_coefficient_derivative_norm_le
    (eta : SymmetricPerturbation) (k : ℕ) (p : Coord) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ k (fun x => perturbationTensor eta x i j) p‖ ≤
      perturbationSeminorm k eta := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    ((norm_nonneg _).trans (perturbation_derivative_norm_le eta k p))
  intro v
  change ‖iteratedFDeriv ℝ k (fun x => eta.val x i j) p v‖ ≤ _
  rw [supportedTensor_coeff_iteratedFDeriv]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k eta.val p v‖ := Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ ‖iteratedFDeriv ℝ k eta.val p‖ * ∏ l, ‖v l‖ :=
      (iteratedFDeriv ℝ k eta.val p).le_opNorm v
    _ ≤ perturbationSeminorm k eta * ∏ l, ‖v l‖ :=
      mul_le_mul_of_nonneg_right (perturbation_derivative_norm_le eta k p)
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _))

theorem perturbedMetric_sub_eq_tensor_sub (g0 : MetricField) (eta theta : SymmetricPerturbation) :
    (fun p => perturbedMetric g0 eta p - perturbedMetric g0 theta p) =
      perturbationTensor (eta - theta) := by
  funext p
  ext i j
  change (g0 p i j + perturbationTensor eta p i j) -
    (g0 p i j + perturbationTensor theta p i j) =
      perturbationTensor eta p i j - perturbationTensor theta p i j
  ring

theorem perturbedMetric_coefficient_sub_eq (g0 : MetricField)
    (eta theta : SymmetricPerturbation) (i j : Fin 2) :
    (fun p => perturbedMetric g0 eta p i j - perturbedMetric g0 theta p i j) =
      (fun p => perturbationTensor (eta - theta) p i j) := by
  funext p
  exact congrFun (congrFun (congrFun (perturbedMetric_sub_eq_tensor_sub g0 eta theta) p) i) j

theorem closure_exists_metric_jet_approximation
    {T : Type*} [TopologicalSpace T] (f : T → SymmetricPerturbation) (hf : Continuous f)
    (g0 : MetricField) {A : Set T} {theta : T} (hclosure : theta ∈ closure A)
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta ∈ A,
      (∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 (f eta) x -
          perturbedMetric g0 (f theta) x) p‖ ≤ epsilon) ∧
      (∀ i j : Fin 2, ∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 (f eta) x i j -
          perturbedMetric g0 (f theta) x i j) p‖ ≤ epsilon) := by
  obtain ⟨eta, heta, hsmall⟩ := closure_exists_finite_seminorm_approximation f hf hclosure n hepsilon
  refine ⟨eta, heta, ?_, ?_⟩
  · intro k hk p
    rw [perturbedMetric_sub_eq_tensor_sub]
    exact (perturbation_derivative_norm_le (f eta - f theta) k p).trans (hsmall k hk).le
  · intro i j k hk p
    rw [perturbedMetric_coefficient_sub_eq]
    exact (perturbation_coefficient_derivative_norm_le (f eta - f theta) k p i j).trans (hsmall k hk).le

end SmoothLocal.Perturbation

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

theorem exists_N_before_delta_eventually_mem {O : Set SymmetricPerturbation}
    (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1 / 10) (hq : |q0| * a < 1 / 10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℝ in atTop, 1 ≤ tau ∧
        ∃ ρ : SymmetricPerturbation,
          perturbationTensor ρ = pulseTensor q0 a N delta tau ∧ η + ρ ∈ O := by
  obtain ⟨N, epsilon, hN, heps, hball⟩ := exists_ordered_seminorm_neighborhood hO hη
  refine ⟨N, hN, ?_⟩
  intro delta hd
  filter_upwards [eventually_ge_atTop (1 : ℝ), pulse_support_eventually q0 a delta hq,
    pulse_finite_derivative_bounds_eventually q0 a ha delta N heps] with tau ht hshape hsmall
  let ρ : SymmetricPerturbation :=
    supportedPulse q0 a N delta tau ha hd (lt_of_lt_of_le zero_lt_one ht) hax hshape.le
  refine ⟨ht, ρ, rfl, hball ρ ?_⟩
  intro k hk
  exact (supportedPulse_seminorm_le q0 a ha N delta hd ht hax hshape.le k).trans_lt
    (hsmall k (Finset.mem_range.mpr hk))

theorem exists_N_before_delta_eventually_testMetric (g0 : MetricField)
    {O : Set SymmetricPerturbation} (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1 / 10) (hq : |q0| * a < 1 / 10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℝ in atTop, 1 ≤ tau ∧
        ∃ θ ∈ O, perturbedMetric g0 θ = testMetric (perturbedMetric g0 η) q0 a N delta tau := by
  obtain ⟨N, hN, hmem⟩ := exists_N_before_delta_eventually_mem hO hη q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hd
  filter_upwards [hmem delta hd] with tau ht
  obtain ⟨ρ, hρ, hOρ⟩ := ht.2
  refine ⟨ht.1, η + ρ, hOρ, ?_⟩
  ext p i j
  change g0 p i j + (perturbationTensor η p i j + perturbationTensor ρ p i j) =
    (g0 p i j + perturbationTensor η p i j) + pulseTensor q0 a N delta tau p i j
  rw [hρ]
  ring

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseNeighborhoodAdapters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem exists_N_before_delta_eventually_integer_testMetric (g0 : MetricField)
    {O : Set SymmetricPerturbation} (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1/10) (hq : |q0| *a < 1/10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧
        ∃ θ ∈ O, perturbedMetric g0 θ =
          testMetric (perturbedMetric g0 η) q0 a N delta (tau : ℝ) := by
  obtain ⟨N, hN, hmem⟩ := exists_N_before_delta_eventually_testMetric g0 hO hη q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hd
  exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
    (hmem delta hd)

theorem exists_N_before_delta_eventually_positive_testMetric
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {O : Set SymmetricPerturbation} (hO : IsOpen O) {η : SymmetricPerturbation}
    (hη : η ∈ O) (hηmetric : η ∈ metricPatchSet g0 kappa)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1/10) (hq : |q0| *a < 1/10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧
        ∃ θ : SymmetricPerturbation, θ ∈ O ∧ θ ∈ metricPatchSet g0 kappa ∧
          perturbedMetric g0 θ = testMetric (perturbedMetric g0 η) q0 a N delta (tau : ℝ) ∧
          SmoothPositiveOn (testMetric (perturbedMetric g0 η) q0 a N delta (tau : ℝ)) U ∧
          ∀ p ∈ centralBox,
            gaussianCurvature (testMetric (perturbedMetric g0 η) q0 a N delta (tau : ℝ)) p < -kappa/2 := by
  have hOmetric : IsOpen (O ∩ metricPatchSet g0 kappa) :=
    hO.inter (metricPatchSet_isOpen hg0 hU hSU kappa)
  obtain ⟨N, hN, hmem⟩ := exists_N_before_delta_eventually_integer_testMetric g0
    hOmetric ⟨hη, hηmetric⟩ q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hd
  filter_upwards [hmem delta hd] with tau ht
  obtain ⟨θ, hθ, heq⟩ := ht.2
  have hpositive : SmoothPositiveOn (perturbedMetric g0 θ) U :=
    perturbedMetric_smoothPositiveOn hg0 θ hθ.2.1
  have hcentral : ∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 θ) p < -kappa/2 := hθ.2.2
  refine ⟨ht.1, θ, hθ.1, hθ.2, heq, ?_, ?_⟩
  · rwa [← heq]
  · rwa [← heq]

theorem exists_N_before_delta_eventually_relative_metric_neighborhood
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O)
    {η : metricPatchSet g0 kappa} (hη : η ∈ O)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1/10) (hq : |q0| *a < 1/10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧
        ∃ θ : metricPatchSet g0 kappa, θ ∈ O ∧
          perturbedMetric g0 θ.val = testMetric (perturbedMetric g0 η.val) q0 a N delta (tau : ℝ) ∧
          SmoothPositiveOn (testMetric (perturbedMetric g0 η.val) q0 a N delta (tau : ℝ)) U ∧
          ∀ p ∈ centralBox,
            gaussianCurvature (testMetric (perturbedMetric g0 η.val) q0 a N delta (tau : ℝ)) p < -kappa/2 := by
  have hOa : IsOpen (Subtype.val '' O : Set SymmetricPerturbation) :=
    (metricPatchSet_isOpen hg0 hU hSU kappa).isOpenMap_subtype_val O hO
  have hηa : η.val ∈ (Subtype.val '' O : Set SymmetricPerturbation) := ⟨η, hη, rfl⟩
  obtain ⟨N, hN, hmem⟩ := exists_N_before_delta_eventually_positive_testMetric hg0 hU hSU
    hOa hηa η.property q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hd
  filter_upwards [hmem delta hd] with tau ht
  obtain ⟨θ, hθO, hθmetric, heq, hpositive, hcentral⟩ := ht.2
  obtain ⟨θ', hθ', hvalue⟩ := hθO
  refine ⟨ht.1, θ', hθ', ?_, hpositive, hcentral⟩
  simpa only [hvalue] using heq

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

theorem relative_closure_exists_metric_approximation
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U)
    {A : Set (metricPatchSet g0 kappa)} {theta : metricPatchSet g0 kappa}
    (hclosure : theta ∈ closure A) (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta : metricPatchSet g0 kappa, eta ∈ A ∧
      SmoothPositiveOn (perturbedMetric g0 eta.val) U ∧
      (∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 eta.val) p < -kappa / 2) ∧
      (∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x -
          perturbedMetric g0 theta.val x) p‖ ≤ epsilon) ∧
      (∀ i j : Fin 2, ∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x i j -
          perturbedMetric g0 theta.val x i j) p‖ ≤ epsilon) := by
  obtain ⟨eta, heta, hT, hC⟩ := closure_exists_metric_jet_approximation
    (Subtype.val : metricPatchSet g0 kappa → SymmetricPerturbation) continuous_subtype_val
    g0 hclosure n hepsilon
  exact ⟨eta, heta, perturbedMetric_smoothPositiveOn hg0 eta.val eta.property.1,
    eta.property.2, hT, hC⟩

theorem exists_N_before_delta_eventually_class_approximation
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {A O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O)
    {etaStar : metricPatchSet g0 kappa} (hStar : etaStar ∈ O)
    (hOclosure : O ⊆ closure A)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1 / 10) (hq : |q0| * a < 1 / 10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 0 < tau ∧
        ∃ eta : metricPatchSet g0 kappa, eta ∈ A ∧
          SmoothPositiveOn (perturbedMetric g0 eta.val) U ∧
          (∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 eta.val) p < -kappa / 2) ∧
          (∀ k ≤ tau, ∀ p : Coord,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x -
              testMetric (perturbedMetric g0 etaStar.val) q0 a N delta (tau : ℝ) x) p‖ ≤
                metricApproximationAccuracy tau) ∧
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p : Coord,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x i j -
              testMetric (perturbedMetric g0 etaStar.val) q0 a N delta (tau : ℝ) x i j) p‖ ≤
                metricApproximationAccuracy tau) := by
  obtain ⟨N, hN, hpulse⟩ := exists_N_before_delta_eventually_relative_metric_neighborhood
    hg0 hU hSU hO hStar q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hdelta
  filter_upwards [hpulse delta hdelta] with tau htau
  have hpositive : 0 < tau := by
    have hh : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le htau.1
    exact_mod_cast hh
  obtain ⟨theta, hthetaO, hthetaEq, hthetaPositive, hthetaCentral⟩ := htau.2
  obtain ⟨eta, heta, hmetric, hcentral, hT, hC⟩ :=
    relative_closure_exists_metric_approximation hg0 (hOclosure hthetaO) tau
      (metricApproximationAccuracy_pos hpositive)
  refine ⟨hpositive, eta, heta, hmetric, hcentral, ?_, ?_⟩
  · simpa only [hthetaEq] using hT
  · simpa only [hthetaEq] using hC

end SmoothLocal.Pulse

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

theorem fixed_metric_finite_coefficient_jet_bound
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U)
    (hU : IsOpen U) (hSU : modelSquare ⊆ U) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ B := by
  classical
  have hco : ∀ i j : Fin 2, ∃ A : ℝ, 0 ≤ A ∧
      ∀ k ≤ m, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ A :=
    fun i j => compact_finite_fullJet_bound (hg.1 i j) hU modelSquare_isCompact hSU m
  choose A hA0 hA using hco
  refine ⟨∑ i : Fin 2, ∑ j : Fin 2, A i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hA0 i j)),?_⟩
  intro i j k hk p hp
  exact (hA i j k hk p hp).trans
    ((Finset.single_le_sum (fun j _ => hA0 i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => hA0 a b))
        (Finset.mem_univ i)))

theorem metric_jet_norm_le_of_approximation_locality
    {gStar gTau test : MetricField} {U V : Set Coord}
    (hgStar : SmoothPositiveOn gStar U) (hgTau : SmoothPositiveOn gTau V)
    (hU : IsOpen U) (hV : IsOpen V) {p : Coord} (hpU : p ∈ U) (hpV : p ∈ V)
    (heq : test =ᶠ[𝓝 p] gStar) (i j : Fin 2) (k : ℕ) {B epsilon : ℝ}
    (hbase : ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ B)
    (happrox : ‖iteratedFDeriv ℝ k (fun q => gTau q i j-test q i j) p‖ ≤ epsilon) :
    ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ B+epsilon := by
  have heqCoeff : (fun q => gTau q i j-test q i j) =ᶠ[𝓝 p]
      (fun q => gTau q i j-gStar q i j) := by
    filter_upwards [metric_coeff_eventuallyEq heq i j] with q hq
    rw [hq]
  have hdiff : ‖iteratedFDeriv ℝ k (fun q => gTau q i j-gStar q i j) p‖ ≤ epsilon := by
    rw [←(heqCoeff.iteratedFDeriv ℝ k).self_of_nhds]
    exact happrox
  have hsplit := iteratedFDeriv_sub_apply (i := k)
    (((hgTau.1 i j).contDiffAt (hV.mem_nhds hpV)).of_le (WithTop.coe_le_coe.mpr le_top))
    (((hgStar.1 i j).contDiffAt (hU.mem_nhds hpU)).of_le (WithTop.coe_le_coe.mpr le_top))
  change ‖iteratedFDeriv ℝ k ((fun q => gTau q i j)-(fun q => gStar q i j)) p‖ ≤ epsilon at hdiff
  rw [hsplit] at hdiff
  calc
    _ = ‖(iteratedFDeriv ℝ k (fun q => gTau q i j) p-
        iteratedFDeriv ℝ k (fun q => gStar q i j) p)+
          iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ := by rw [sub_add_cancel]
    _ ≤ ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p-
        iteratedFDeriv ℝ k (fun q => gStar q i j) p‖+
          ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ := norm_add_le _ _
    _ ≤ epsilon+B := add_le_add hdiff hbase
    _ = B+epsilon := add_comm _ _

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_OffPulseMetricBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Hyperbolic

theorem testMetric_eventuallyEq_off_pulse
    (gStar : MetricField) (q0 a : ℝ) (N : ℕ) {delta tau : ℝ}
    (ha : 0 < a) (hd : 0 < delta) (ht : 0 < tau) {p : Coord}
    (hfar : delta/tau ≤ |p 1+q0*p 0|) :
    testMetric gStar q0 a N delta tau =ᶠ[𝓝 p] gStar := by
  apply metric_add_eventuallyEq_of_not_mem_tsupport gStar (pulseTensor q0 a N delta tau)
  intro hp
  have hbox := pulseTensor_tsupport_subset ha hd ht N hp
  have hnear := (pulseOriginalBox_coordinate_bounds hbox).2
  have hpos : 0 < delta/tau := div_pos hd ht
  have he : delta/(2*tau) = (delta/tau)/2 := by ring
  rw [he] at hnear
  linarith

theorem testMetric_eventuallyEq_below_pulse
    (gStar : MetricField) (q0 a : ℝ) (N : ℕ) {delta tau x t : ℝ}
    (ha : 0 < a) (hd : 0 < delta) (htau : 0 < tau) (ht : t ≤ -delta/tau) :
    testMetric gStar q0 a N delta tau =ᶠ[𝓝 (inverseShearCoordinates q0 ![x,t])] gStar := by
  apply testMetric_eventuallyEq_off_pulse gStar q0 a N ha hd htau
  have he : (inverseShearCoordinates q0 ![x,t]) 1+
      q0*(inverseShearCoordinates q0 ![x,t]) 0 = t := by
    simp [inverseShearCoordinates]
  rw [he]
  have hwidth : delta/tau ≤ -t := by
    simpa only [neg_div, neg_neg] using neg_le_neg ht
  exact hwidth.trans (neg_le_abs t)

theorem exists_uniform_off_pulse_metric_jets
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {q0 L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
      ∀ tau : ℕ, 1 ≤ tau → m ≤ tau →
      ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
      (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
          testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
      ∀ x t : ℝ, |x| ≤ L*r → t ∈ Icc (-r) (-delta/(tau : ℝ)) →
      ∀ i j : Fin 2, ∀ k ≤ m,
        ‖iteratedFDeriv ℝ k (fun p => gTau p i j) (inverseShearCoordinates q0 ![x,t])‖ ≤ B := by
  obtain ⟨Bstar,hBstar,hbase⟩ := fixed_metric_finite_coefficient_jet_bound hgStar hV hSV m
  refine ⟨Bstar+1, by linarith, ?_⟩
  intro N delta hd tau htau hmtau gTau U hgTau hU hSU happrox x t hx ht i j k hk
  have htr : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast htau)
  have hneg : -delta/(tau : ℝ) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hd) htr
  have hpS : inverseShearCoordinates q0 ![x,t] ∈ modelSquare := by
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨hx, abs_le.mpr ⟨ht.1, (ht.2.trans hneg.le).trans hr.le⟩⟩
  have heq := testMetric_eventuallyEq_below_pulse gStar q0 (L*r/16) N
    (x := x) (div_pos (mul_pos hL hr) (by norm_num)) hd htr ht.2
  have hb := metric_jet_norm_le_of_approximation_locality hgStar hgTau hV hU
    (hSV hpS) (hSU hpS) heq i j k (hbase i j k hk _ hpS)
    (happrox i j k (hk.trans hmtau) _ hpS)
  exact hb.trans (add_le_add le_rfl (metricApproximationAccuracy_le_one htau))

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_ShearedMetricFiniteJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Hyperbolic

theorem exists_uniform_off_pulse_sheared_metric_bounds
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {q0 L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
      ∀ tau : ℕ, 1 ≤ tau → m ≤ tau →
      ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
      (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
          testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
      ∀ i j : Fin 2, CoordinateBound (fun p => metricInShearCoordinates gTau q0 p i j)
        {p | |p 0| ≤ L*r ∧ p 1 ∈ Icc (-r) (-delta/(tau : ℝ))} m B := by
  obtain ⟨B,hB,hjets⟩ := exists_uniform_off_pulse_metric_jets hgStar hV hSV
    hL hr hrhalf hLr hq0 m
  refine ⟨shearedMetricCoordinateBudget B q0 m,
    shearedMetricCoordinateBudget_nonneg q0 m hB,?_⟩
  intro N delta hd tau htau hmtau gTau U hgTau hU hSU happrox
  let T : Set Coord := {p | |p 0| ≤ L*r ∧ p 1 ∈ Icc (-r) (-delta/(tau : ℝ))}
  let S : Set Coord := inverseShearCoordinates q0 '' T
  have htr : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast htau)
  have ht0 : -delta/(tau : ℝ) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hd) htr
  have hpS (p : Coord) (hp : p ∈ T) : inverseShearCoordinates q0 p ∈ modelSquare := by
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨hp.1,abs_le.mpr ⟨hp.2.1,(hp.2.2.trans ht0.le).trans hr.le⟩⟩
  have hsub : S ⊆ U := by
    rintro y ⟨p,hp,rfl⟩
    exact hSU (hpS p hp)
  have hb (i j : Fin 2) : CoordinateBound (fun p => gTau p i j) S m B := by
    apply coordinateBound_of_frechet_bounds (hgTau.1 i j) hU hsub
    intro k hk y hy
    obtain ⟨p,hp,rfl⟩ := hy
    have he : ![p 0,p 1] = p := by ext a; fin_cases a <;> rfl
    simpa only [he] using hjets N delta hd tau htau hmtau gTau U hgTau hU hSU happrox
      (p 0) (p 1) hp.1 hp.2 i j k hk
  have hs := metric_coordinate_bound_inverse_shear hgTau hU hsub hB hb q0
  intro i j ds hds p hp
  exact hs i j ds hds p ⟨p,hp,rfl⟩

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_BoundedClassCapData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow

theorem bounded_class_actual_cap_data
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (eta : metricPatchSet g0 kappa) {z : Coord → ℝ} {M : ℕ}
    (hclass : BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z) :
    ∃ U : Set Coord, IsOpen U ∧ modelSquare ⊆ U ∧ U ⊆ V ∧
      SmoothPositiveOn g0 U ∧ SmoothPositiveOn (perturbedMetric g0 eta.val) U ∧
      CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z := by
  obtain ⟨_,hadm,hjets,hyy,hE⟩ := hclass
  obtain ⟨W,hW,hSW,hg,hz,hD,_,_,hq⟩ := hadm
  let U := W ∩ V
  have hU : IsOpen U := hW.inter hV
  have hSU : modelSquare ⊆ U := fun p hp => ⟨hSW hp,hSV hp⟩
  have hg0U : SmoothPositiveOn g0 U :=
    ⟨fun i j => (hg0.1 i j).mono inter_subset_right,
      fun p hp => hg0.2 p hp.2⟩
  have hgU : SmoothPositiveOn (perturbedMetric g0 eta.val) U :=
    ⟨fun i j => (hg.1 i j).mono inter_subset_left,
      fun p hp => hg.2 p hp.1⟩
  refine ⟨U,hU,hSU,inter_subset_right,hg0U,hgU,?_⟩
  exact ⟨hz.mono inter_subset_left,hjets,(fun p hp => (hyy p hp).1),hE,hq,hD⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_BoundedClassApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse

theorem exists_N_before_delta_eventually_bounded_height_approximation
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (M : ℕ) (q0 : ℚ)
    {O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O)
    {etaStar : metricPatchSet g0 kappa} (hStar : etaStar ∈ O)
    (hOclosure : O ⊆ closure (boundedHeightClass g0 kappa M q0))
    (a : ℝ) (ha : 0 < a) (hax : a ≤ 1 / 10) (hq : |(q0 : ℝ)| * a < 1 / 10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 0 < tau ∧
        ∃ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z ∧
          |hessianQuotient (perturbedMetric g0 eta.val) z 0 - (q0 : ℝ)| <
            1 / (100 * boundedClassWidth kappa M) ∧
          SmoothPositiveOn (perturbedMetric g0 eta.val) U ∧
          (∀ k ≤ tau, ∀ p : Coord,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x -
              testMetric (perturbedMetric g0 etaStar.val) (q0 : ℝ) a N delta (tau : ℝ) x) p‖ ≤
                metricApproximationAccuracy tau) ∧
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p : Coord,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x i j -
              testMetric (perturbedMetric g0 etaStar.val) (q0 : ℝ) a N delta (tau : ℝ) x i j) p‖ ≤
                metricApproximationAccuracy tau) := by
  obtain ⟨N, hN, happrox⟩ := exists_N_before_delta_eventually_class_approximation
    hg0 hU hSU hO hStar hOclosure (q0 : ℝ) a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hdelta
  filter_upwards [happrox delta hdelta] with tau htau
  obtain ⟨eta, ⟨z, hz, hlabel⟩, hpositive, _, hT, hC⟩ := htau.2
  exact ⟨htau.1, eta, z, hz, hlabel, hpositive, hT, hC⟩

end SmoothLocal.Perturbation

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

theorem comparisonParameterDomain_isOpen {g : MetricField} {P z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U) :
    IsOpen (comparisonParameterDomain g P z U) :=
  (comparisonStateMap_contDiffOn hU hP hz).continuousOn.isOpen_inter_preimage
    (hU.prod isOpen_univ) (darbouxQStateDomain_isOpen hg hU)

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

theorem exists_actual_Q_containing_rectangle
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {R a b : ℝ} (hR : 0 < R) (hab : a ≤ b)
    (hbox : closedRectangle (-R) R a b ⊆ U)
    (hxx : ∀ p ∈ closedRectangle (-R) R a b, covHessian g z p 0 0 ≠ 0) :
    ∃ radius lo hi : ℝ, R < radius ∧ lo < a ∧ b < hi ∧
      coordinateRectangle radius lo hi ⊆ U ∧
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) := by
  let V := U ∩ (fun p => covHessian g z p 0 0) ⁻¹' ({0}ᶜ : Set ℝ)
  have hV : IsOpen V := (covHessian_contDiffOn hg hU hz 0 0).continuousOn.isOpen_inter_preimage hU
    isClosed_singleton.isOpen_compl
  have hsub : closedRectangle (-R) R a b ⊆ V := by
    intro p hp
    exact ⟨hbox hp,hxx p hp⟩
  obtain ⟨radius,lo,hi,hr,hl,hh,hVU⟩ := exists_containing_coordinateRectangle hV hR hab hsub
  exact ⟨radius,lo,hi,hr,hl,hh,fun p hp => (hVU hp).1,fun p hp => (hVU hp).2⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_ActualFiniteShearedCutBounds
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

theorem inverseShear_lower_cut_mem_modelSquare
    {q0 L r x : ℝ} (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20) (hx : |x| ≤ L*r) :
    inverseShearCoordinates q0 (boxPoint x (-r)) ∈ modelSquare := by
  have hx20 : |x| ≤ 1/20 := hx.trans hLr
  have hmul : |q0*x| ≤ (1/20 : ℝ)*(1/20) := by
    rw [abs_mul]
    exact mul_le_mul hq0 hx20 (abs_nonneg x) (by norm_num)
  have hy : |-r-q0*x| ≤ r+(1/20 : ℝ)*(1/20) := by
    calc
      _ ≤ |-r| + |q0*x| := abs_sub _ _
      _ = r + |q0*x| := by rw [abs_neg, abs_of_pos hr]
      _ ≤ _ := add_le_add le_rfl hmul
  have hx3 : |x| ≤ 3 := hx20.trans (by norm_num)
  have hy3 : |-r-q0*x| ≤ 3 := hy.trans (by linarith)
  obtain ⟨hxl,hxr⟩ := abs_le.mp hx3
  obtain ⟨hyl,hyr⟩ := abs_le.mp hy3
  constructor
  · intro i
    fin_cases i
    · simpa [inverseShearCoordinates,boxPoint] using hxl
    · simpa [inverseShearCoordinates,boxPoint] using hyl
  · intro i
    fin_cases i
    · simpa [inverseShearCoordinates,boxPoint] using hxr
    · simpa [inverseShearCoordinates,boxPoint] using hyr

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_CurvatureFullJetComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem metric_word_difference_le_full_jet
    {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j : Fin 2) (ds : List (Fin 2)) {e : ℝ}
    (hjet : ‖iteratedFDeriv ℝ ds.length (fun q => g q i j - h q i j) p‖ ≤ e) :
    |iteratedCoordPartial ds (fun q => g q i j) p -
      iteratedCoordPartial ds (fun q => h q i j) p| ≤ e := by
  rw [← CoordinateBound.iterated_sub (hg.1 i j) (hh.1 i j) hU ds hp]
  exact (norm_iteratedCoordPartial_le_jet ((hg.1 i j).sub (hh.1 i j)) hU ds hp).trans hjet

theorem actual_first_input_difference_le_full_jets
    {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {e : ℝ} (he : 0 ≤ e)
    (hjet : ∀ i j : Fin 2, ∀ k ≤ 1,
      ‖iteratedFDeriv ℝ k (fun q => g q i j - h q i j) p‖ ≤ e) :
    ‖actualCurvatureFirstInput g p - actualCurvatureFirstInput h p‖ ≤ e := by
  change max
    ‖(fun i j => g p i j) - (fun i j => h p i j)‖
    ‖(fun d i j => coordPartial d (fun q => g q i j) p) -
      (fun d i j => coordPartial d (fun q => h q i j) p)‖ ≤ e
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    exact metric_word_difference_le_full_jet hg hh hU hp i j [] (hjet i j 0 (by omega))
  · apply (pi_norm_le_iff_of_nonneg he).mpr
    intro d
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    exact metric_word_difference_le_full_jet hg hh hU hp i j [d] (hjet i j 1 (by omega))

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

theorem actual_sheared_reference_first_distance_of_locality
    {gStar gTau test : MetricField} {U V : Set Coord}
    (hgTau : SmoothPositiveOn gTau U) (hgStar : SmoothPositiveOn gStar V)
    (hU : IsOpen U) (hV : IsOpen V) {q0 e : ℝ} (hq0 : |q0| ≤ 1) (he : 0 ≤ e)
    {p : Coord} (hpU : inverseShearCoordinates q0 p ∈ U) (hpV : inverseShearCoordinates q0 p ∈ V)
    (hlocal : test =ᶠ[𝓝 (inverseShearCoordinates q0 p)] gStar)
    (happrox : ∀ i j : Fin 2, ∀ k ≤ 1,
      ‖iteratedFDeriv ℝ k (fun q => gTau q i j - test q i j) (inverseShearCoordinates q0 p)‖ ≤ e) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p -
      actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p‖ ≤ 8 * e := by
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hgTW : SmoothPositiveOn gTau W :=
    ⟨fun i j => (hgTau.1 i j).mono inter_subset_left, fun q hq => hgTau.2 q hq.1⟩
  have hgSW : SmoothPositiveOn gStar W :=
    ⟨fun i j => (hgStar.1 i j).mono inter_subset_right, fun q hq => hgStar.2 q hq.2⟩
  have hpW : inverseShearCoordinates q0 p ∈ W := ⟨hpU, hpV⟩
  have hdiff : ∀ i j : Fin 2, ∀ k ≤ 1,
      ‖iteratedFDeriv ℝ k (fun q => gTau q i j - gStar q i j) (inverseShearCoordinates q0 p)‖ ≤ e := by
    intro i j k hk
    have heq : (fun q => gTau q i j - test q i j) =ᶠ[𝓝 (inverseShearCoordinates q0 p)]
        (fun q => gTau q i j - gStar q i j) := by
      filter_upwards [metric_coeff_eventuallyEq hlocal i j] with q hq
      rw [hq]
    rw [← (heq.iteratedFDeriv ℝ k).self_of_nhds]
    exact happrox i j k hk
  have hfirst := actual_first_input_difference_le_full_jets hgTW hgSW hW hpW he hdiff
  rw [norm_sub_rev]
  exact actual_shear_first_jet_distance_le hgTW hgSW hW hq0 hpW hfirst

theorem actual_pulse_edge_reference_first_distance
    {gStar gTau : MetricField} {U V : Set Coord}
    (hgTau : SmoothPositiveOn gTau U) (hgStar : SmoothPositiveOn gStar V)
    (hU : IsOpen U) (hV : IsOpen V) {q0 a delta : ℝ} {N tau : ℕ}
    (hq0 : |q0| ≤ 1) (ha : 0 < a) (hd : 0 < delta) (htau : 1 ≤ tau)
    {x : ℝ}
    (hpU : inverseShearCoordinates q0 ![x, -delta / (tau : ℝ)] ∈ U)
    (hpV : inverseShearCoordinates q0 ![x, -delta / (tau : ℝ)] ∈ V)
    (happrox : ∀ i j : Fin 2, ∀ k ≤ tau,
      ‖iteratedFDeriv ℝ k
        (fun q => gTau q i j - testMetric gStar q0 a N delta (tau : ℝ) q i j)
        (inverseShearCoordinates q0 ![x, -delta / (tau : ℝ)])‖ ≤ metricApproximationAccuracy tau) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0) ![x, -delta / (tau : ℝ)] -
      actualCurvatureFirstInput (metricInShearCoordinates gTau q0) ![x, -delta / (tau : ℝ)]‖ ≤
      8 * metricApproximationAccuracy tau := by
  have htauR : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le (by exact_mod_cast htau)
  apply actual_sheared_reference_first_distance_of_locality hgTau hgStar hU hV hq0
    (metricApproximationAccuracy_pos htau).le hpU hpV
    (testMetric_eventuallyEq_below_pulse gStar q0 a N ha hd htauR le_rfl)
  intro i j k hk
  exact happrox i j k (hk.trans htau)

end SmoothLocal.Pulse

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

theorem norm_verticalJet_fullJet_le {f : Coord → ℝ} {V : Set Coord}
    (hf : ContDiffOn ℝ ∞ f V) (hV : IsOpen V) {p : Coord} (hp : p ∈ V)
    (n k : ℕ) :
    ‖iteratedFDeriv ℝ k (verticalJet f n) p‖ ≤ ‖iteratedFDeriv ℝ (k + n) f p‖ := by
  induction n generalizing k with
  | zero => simpa only [verticalJet, Nat.add_zero] using le_rfl
  | succ n hn =>
    have hb := (norm_iteratedFDeriv_coordPartial_le (verticalJet_contDiffOn hV hf n)
      hV hp 1 k).trans (hn (k + 1))
    have he : k + 1 + n = k + (n + 1) := by omega
    rw [he] at hb
    exact hb

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonUpperVelocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Taylor

theorem comparison_upper_velocity_jet_bound {P z : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (hU : IsOpen U) (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (b : ℝ) (hupper : ∀ x ∈ I, (![x,b] : Coord) ∈ U) {x : ℝ} (hx : x ∈ I)
    (N : ℕ) {BZ BP : ℝ}
    (hZB : ‖iteratedFDeriv ℝ N (heightCauchyVelocity z b) x‖ ≤ BZ)
    (hPB : ‖iteratedFDeriv ℝ N (heightCauchyVelocity P b) x‖ ≤ BP) :
    ‖iteratedFDeriv ℝ N (heightCauchyVelocity (comparisonDifference P z) b) x‖ ≤ BZ+BP := by
  have hzv := heightCauchyVelocity_contDiffOn hz hU b hupper
  have hPv := heightCauchyVelocity_contDiffOn hP hU b hupper
  have heq : heightCauchyVelocity (comparisonDifference P z) b =ᶠ[𝓝 x]
      (heightCauchyVelocity z b-heightCauchyVelocity P b) := by
    filter_upwards [hI.mem_nhds hx] with y hy
    exact CoordinateBound.iterated_sub hz hP hU [1] (hupper y hy)
  rw [(heq.iteratedFDeriv ℝ N).self_of_nhds,iteratedFDeriv_sub_apply
    ((hzv.contDiffAt (hI.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr le_top))
    ((hPv.contDiffAt (hI.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr le_top))]
  exact (norm_sub_le _ _).trans (add_le_add hZB hPB)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_ActualCentralShearMargins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

theorem bounded_class_sheared_C3_on_actual_region
    {g : MetricField} {z : Coord → ℝ} {M : ℕ}
    (hclass : BoundedAdmissibleHeight g M z) (q0 : ℝ) {S : Set Coord}
    (hS : ∀ p ∈ S, inverseShearCoordinates q0 p ∈ modelSquare) :
    CoordinateBound (heightInShearCoordinates z q0) S 3 ((2*(1+|q0|))^3*(M : ℝ)) := by
  obtain ⟨_,hadm,hjet,_,_⟩ := hclass
  obtain ⟨U,hU,hSU,_,hz,_,_,_,_⟩ := hadm
  have hzB : CoordinateBound z modelSquare 3 (M : ℝ) := by
    intro ds hds p hp
    exact (norm_iteratedCoordPartial_le_jet hz hU ds (hSU hp)).trans
      (hjet ds.length (by omega) p hp)
  have hs := SmoothLocal.Pulse.CoordinateBound.inverse_shear hzB hz hU hSU (Nat.cast_nonneg M) q0
  intro ds hds p hp
  exact hs ds hds p (hS p hp)

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_PatchAddressModel
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

theorem patchAddressModelDomain_mapsTo_square (a : PatchAddress) :
    MapsTo (affineCoordinates (patchAddressCenter a) (patchAddressMatrix a)) patchAddressModelDomain square := by
  intro q hq
  apply patch_core_image_mem_square a.1 a.2.1 a.2.2.1 a.2.2.2.val a.2.2.2.property
  exact (by simpa only [patchAddressModelDomain,Metric.mem_ball,dist_zero_right] using hq : ‖q‖ < 13/4).le

theorem patchAddressInitialMetric_smoothPositive (a : PatchAddress) :
    SmoothPositiveOn (patchAddressInitialMetric a) patchAddressModelDomain := by
  have h := affinePullbackMetric_smoothPositive initialAssemblyMetric_smoothPositiveOn
    (patchAddressCenter a) (patchAddressMatrix a) (Matrix.mulVec_injective_of_isUnit (patchAddressMatrix_isUnit a))
  exact ⟨fun i j => (h.1 i j).mono (patchAddressModelDomain_mapsTo_square a),
    fun p hp => h.2 p (patchAddressModelDomain_mapsTo_square a hp)⟩

theorem patchAddressInitialMetric_curvature (a : PatchAddress) {p : Coord}
    (hp : p ∈ patchAddressModelDomain) :
    gaussianCurvature (patchAddressInitialMetric a) p = modelCurvature (patchAddressAmplitude a) p := by
  apply initialAssemblyMetric_model_in_patch_coordinates a.1 a.2.1 a.2.2.1 a.2.2.2.val a.2.2.2.property
  exact (by simpa only [patchAddressModelDomain,Metric.mem_ball,dist_zero_right] using hp : ‖p‖ < 13/4).le

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_ActualLowMetricBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem pulseTensor_coeff_derivative_le (q0 a : ℝ) (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (i j : Fin 2) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta tau q i j) p‖ ≤
      pulseDerivativeBound q0 a ha delta k*tau^k/tau^N := by
  let L : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ := metricCoefficientCLM i j
  have h := L.norm_iteratedFDeriv_comp_left (pulseTensor_contDiff q0 a N delta tau).contDiffAt
    (WithTop.coe_le_coe.mpr le_top) (n := k) (x := p)
  change ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta tau q i j) p‖ ≤
    ‖L‖*‖iteratedFDeriv ℝ k (pulseTensor q0 a N delta tau) p‖ at h
  exact h.trans ((mul_le_mul_of_nonneg_right (metricCoefficientCLM_norm_le i j)
    (norm_nonneg _)).trans (by simpa only [one_mul] using
      pulseTensor_derivative_le q0 a ha N delta ht k p))

theorem pulseTensor_finite_coeff_jets_eventually_small
    (q0 a : ℝ) (ha : 0 < a) (m N : ℕ) (hmN : m < N) (delta : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ tau : ℕ in atTop, 1 ≤ tau ∧ ∀ i j : Fin 2, ∀ k ≤ m, ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta (tau : ℝ) q i j) p‖ ≤ epsilon := by
  have heach (k : Fin (m+1)) : ∀ᶠ tau : ℕ in atTop,
      pulseDerivativeBound q0 a ha delta k.val*(tau : ℝ)^k.val/(tau : ℝ)^N < epsilon :=
    ((fixed_order_pulse_bound_tendsto_zero q0 a ha delta N k.val (by omega)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop)).eventually
        (eventually_lt_nhds hepsilon)
  have hall : ∀ᶠ tau : ℕ in atTop, ∀ k : Fin (m+1),
      pulseDerivativeBound q0 a ha delta k.val*(tau : ℝ)^k.val/(tau : ℝ)^N < epsilon :=
    Filter.eventually_all.mpr heach
  filter_upwards [eventually_ge_atTop 1,hall] with tau htau hbound
  refine ⟨htau,?_⟩
  intro i j k hk p
  have hkBound := hbound ⟨k,by omega⟩
  change pulseDerivativeBound q0 a ha delta k*(tau : ℝ)^k/(tau : ℝ)^N < epsilon at hkBound
  exact (pulseTensor_coeff_derivative_le q0 a ha N delta (by exact_mod_cast htau) i j k p).trans
    hkBound.le

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_ActualTestMetricPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem testMetric_coeff_contDiffOn {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun q => testMetric gStar q0 a N delta tau q i j) V := by
  have hp : ContDiff ℝ ∞ (fun q => pulseTensor q0 a N delta tau q i j) :=
    (contDiff_apply ℝ ℝ j).comp
      ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (pulseTensor_contDiff q0 a N delta tau))
  exact (hgStar.1 i j).add hp.contDiffOn

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Obstructions_BoundedClassTopology
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Flow

theorem boundedHeightClass_nonempty_parameters
    {g0 : MetricField} {kappa : ℝ} {M : ℕ} {q0 : ℚ}
    (hclass : (boundedHeightClass g0 kappa M q0).Nonempty) :
    0 < M ∧ |(q0 : ℝ)| < 1/20 := by
  obtain ⟨eta,z,hz,hcenter⟩ := hclass
  exact ⟨hz.1,boundedHeightClass_label_abs_lt ⟨eta,z,hz,hcenter⟩⟩

theorem boundedHeightClass_closure_parameters
    {g0 : MetricField} {kappa : ℝ} {M : ℕ} {q0 : ℚ}
    {eta : metricPatchSet g0 kappa}
    (heta : eta ∈ closure (boundedHeightClass g0 kappa M q0)) :
    0 < M ∧ |(q0 : ℝ)| < 1/20 :=
  boundedHeightClass_nonempty_parameters (Set.Nonempty.of_closure ⟨eta,heta⟩)

theorem bounded_class_open_closure_pulse_family_at_radius
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (M : ℕ) (q0 : ℚ)
    {O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O)
    {etaStar : metricPatchSet g0 kappa} (hStar : etaStar ∈ O)
    (hOclosure : O ⊆ closure (boundedHeightClass g0 kappa M q0))
    {r : ℝ} (hr : 0 < r) (hLr : boundedClassWidth kappa M*r ≤ 1/20) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 0 < tau ∧
        ∃ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z ∧
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-(q0 : ℝ)| ≤
            1/(100*boundedClassWidth kappa M) ∧
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x i j-
              testMetric (perturbedMetric g0 etaStar.val) (q0 : ℝ)
                (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) x i j) p‖ ≤
                  metricApproximationAccuracy tau) := by
  have hparams := boundedHeightClass_closure_parameters (hOclosure hStar)
  let a := boundedClassWidth kappa M*r/16
  have ha : 0 < a := div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
  have hax : a ≤ 1/10 := by
    dsimp only [a]
    linarith
  have hq : |(q0 : ℝ)| *a < 1/10 := by
    have hm := mul_le_mul hparams.2.le hax ha.le (by norm_num : (0 : ℝ) ≤ 1/20)
    norm_num at hm
    linarith
  obtain ⟨N,hN,hfamily⟩ := exists_N_before_delta_eventually_bounded_height_approximation
    hg0 hV hSV M q0 hO hStar hOclosure a ha hax hq
  refine ⟨N,hN,?_⟩
  intro delta hdelt
  filter_upwards [hfamily delta hdelt] with tau htau
  obtain ⟨eta,z,hclass,hcenter,_,_,hC⟩ := htau.2
  exact ⟨htau.1,eta,z,hclass,hcenter.le,fun i j k hk p _ => hC i j k hk p⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Obstructions_PatchObstructionSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

def patchObstructionSet (g0 : MetricField) (kappa : ℝ) : Set (metricPatchSet g0 kappa) :=
  ⋂ index : ℕ × ℚ, (closure (boundedHeightClass g0 kappa index.1 index.2))ᶜ

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ActualPulseMetricCloseness
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem metric_difference_jet_le_actual_pulse_error
    {gStar gTau : MetricField} {V U : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hgTau : SmoothPositiveOn gTau U)
    (hV : IsOpen V) (hU : IsOpen U) {p : Coord} (hpV : p ∈ V) (hpU : p ∈ U)
    (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (i j : Fin 2) (k : ℕ) {P E : ℝ}
    (hpulse : ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta tau q i j) p‖ ≤ P)
    (herror : ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
      testMetric gStar q0 a N delta tau q i j) p‖ ≤ E) :
    ‖iteratedFDeriv ℝ k (fun q => gTau q i j-gStar q i j) p‖ ≤ P+E := by
  have hps : ContDiff ℝ ∞ (fun q => pulseTensor q0 a N delta tau q i j) :=
    (contDiff_apply ℝ ℝ j).comp
      ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (pulseTensor_contDiff q0 a N delta tau))
  have hbs := (hgStar.1 i j).contDiffAt (hV.mem_nhds hpV)
  have hgs := (hgTau.1 i j).contDiffAt (hU.mem_nhds hpU)
  have hts : ContDiffAt ℝ ∞ (fun q => testMetric gStar q0 a N delta tau q i j) p :=
    hbs.add hps.contDiffAt
  have heq : (fun q => gTau q i j-gStar q i j) =
      (fun q => gTau q i j-testMetric gStar q0 a N delta tau q i j)+
        (fun q => pulseTensor q0 a N delta tau q i j) := by
    funext q
    simp only [testMetric,Pi.add_apply,Matrix.add_apply]
    ring
  rw [heq,iteratedFDeriv_add_apply
    ((hgs.sub hts).of_le (WithTop.coe_le_coe.mpr le_top))
    (hps.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
  exact (norm_add_le _ _).trans ((add_le_add herror hpulse).trans_eq (add_comm E P))

theorem actual_metric_finite_reference_closeness
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (q0 a : ℝ) (ha : 0 < a) (m N : ℕ) (hmN : m < N)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (delta : ℝ) :
    ∀ᶠ tau : ℕ in atTop, 1 ≤ tau ∧ m ≤ tau ∧
      ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
            testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
        ∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => gTau q i j-gStar q i j) p‖ ≤ epsilon := by
  obtain ⟨tau0,_,haccuracy⟩ := exists_first_error_threshold (by positivity : 0 < 4*epsilon)
  filter_upwards [pulseTensor_finite_coeff_jets_eventually_small q0 a ha m N hmN delta
    (half_pos hepsilon),eventually_ge_atTop tau0,eventually_ge_atTop m] with tau hpulse htau hmtau
  refine ⟨hpulse.1,hmtau,?_⟩
  intro gTau U hgTau hU hSU happ i j k hk p hp
  have he : metricApproximationAccuracy tau ≤ epsilon/2 := by linarith [haccuracy tau htau]
  have hb := metric_difference_jet_le_actual_pulse_error hgStar hgTau hV hU
    (hSV hp) (hSU hp) q0 a N delta (tau : ℝ) i j k
    (hpulse.2 i j k hk p) ((happ i j k (hk.trans hmtau) p hp).trans he)
  exact hb.trans_eq (by ring)

theorem actual_sheared_metric_finite_reference_closeness
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {q0 a : ℝ} (hq0 : |q0| ≤ 1) (ha : 0 < a) (m N : ℕ) (hmN : m < N)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (delta : ℝ) :
    ∀ᶠ tau : ℕ in atTop, 1 ≤ tau ∧ m ≤ tau ∧
      ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
            testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
        ∀ i j : Fin 2, ∀ k ≤ m, ∀ p : Coord,
          inverseShearCoordinates q0 p ∈ modelSquare →
          ‖iteratedFDeriv ℝ k (fun q => metricInShearCoordinates gStar q0 q i j-
            metricInShearCoordinates gTau q0 q i j) p‖ ≤ epsilon := by
  let e := epsilon/(4*2^m)
  have he : 0 < e := div_pos hepsilon (by positivity)
  filter_upwards [actual_metric_finite_reference_closeness hgStar hV hSV q0 a ha m N hmN he delta]
    with tau htau
  refine ⟨htau.1,htau.2.1,?_⟩
  intro gTau U hgTau hU hSU happ i j k hk p hp
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hpW : inverseShearCoordinates q0 p ∈ W := ⟨hSU hp,hSV hp⟩
  have hgW (i j : Fin 2) := (hgTau.1 i j).mono (inter_subset_left : W ⊆ U)
  have hsW (i j : Fin 2) := (hgStar.1 i j).mono (inter_subset_right : W ⊆ V)
  have herr (i j : Fin 2) :
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j-gTau q i j) (inverseShearCoordinates q0 p)‖ ≤ e := by
    have hdiff := htau.2.2 gTau U hgTau hU hSU happ i j k hk _ hp
    have heq : (fun q => gStar q i j-gTau q i j) =
        -(fun q => gTau q i j-gStar q i j) := by
      funext point
      simp only [Pi.neg_apply, neg_sub]
    rw [heq,iteratedFDeriv_neg_apply,norm_neg]
    exact hdiff
  have hshear := sheared_metric_full_jet_difference_le hsW hgW hW hq0 he.le hpW k herr i j
  apply hshear.trans
  calc
    4*2^k*e ≤ 4*2^m*e := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) (by norm_num)) he.le
    _ = epsilon := by dsimp only [e]; field_simp

end SmoothLocal.Pulse

end

end OAI
end


