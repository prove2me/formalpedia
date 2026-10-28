-- Prove2me | Definitions.Def_OAIQ038F002
-- name    : OAIQ038F002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:53:10.776307+00:00
-- url     : https://prove2.me/theorems/83dd3678-6d8c-4042-994e-e05ca05743a8
-- title:
--   Definitions bundle OAIQ038F002 of the split of OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 222 declarations of OpenAI's Lean: 134 definitions, 4 instances and 84 theorems. The definitions and types are `OAI.PlanarFalconer.cellsMeeting`, `OAI.PlanarFalconer.circleGraphSignWeight`, `OAI.PlanarFalconer.circlePositivePiece`, `OAI.PlanarFalconer.circleResidualAmplitude`, `OAI.PlanarFalconer.circleStationaryResidual`, `OAI.PlanarFalconer.compactCircleResidual`, `OAI.PlanarFalconer.differenceEnergyMeasure`, `OAI.PlanarFalconer.directStationaryOperator`, `OAI.PlanarFalconer.distanceBinIntegrand`, `OAI.PlanarFalconer.distanceDifferenceKernel`, `OAI.PlanarFalconer.distancePairCells`, `OAI.PlanarFalconer.energyMajorantTerm`, `OAI.PlanarFalconer.fourPairGood`, `OAI.PlanarFalconer.fourSpatialPairEquiv`, `OAI.PlanarFalconer.geometricTree`, `OAI.PlanarFalconer.graphAlgebraicDirection`, `OAI.PlanarFalconer.graphAmplitudeCompact`, `OAI.PlanarFalconer.graphAmplitudePullback`, `OAI.PlanarFalconer.graphAngleCompact`, `OAI.PlanarFalconer.graphAngleCoordinate`, `OAI.PlanarFalconer.graphAngularPullback`, `OAI.PlanarFalconer.graphAngularScale`, `OAI.PlanarFalconer.graphBinPullback`, `OAI.PlanarFalconer.graphCartesianFrequency`, `OAI.PlanarFalconer.graphCellQuadIndices`, `OAI.PlanarFalconer.graphChosenRepresentative`, `OAI.PlanarFalconer.graphComplexCoordinate`, `OAI.PlanarFalconer.graphConePullback`, `OAI.PlanarFalconer.graphDirection`, `OAI.PlanarFalconer.graphDistanceEligibleIndices`, `OAI.PlanarFalconer.graphFixedSign`, `OAI.PlanarFalconer.graphFourSymbolProduct`, `OAI.PlanarFalconer.graphGlobalAnnulus`, `OAI.PlanarFalconer.graphGlobalSlice`, `OAI.PlanarFalconer.graphLiftMap`, `OAI.PlanarFalconer.graphNonedgeIndices`, `OAI.PlanarFalconer.graphNormalizedAxis`, `OAI.PlanarFalconer.graphOriginalKernel`, `OAI.PlanarFalconer.graphOriginalTerm`, `OAI.PlanarFalconer.graphPlaneAngle` and 94 more.
--
--   **Sources.** They come from these modules of lean/OAI/MeasureTheory/Falconer, in whole or in part: `Falconer_Angular_ActualAngleMasks`, `Falconer_Angular_AngleCoordinateTests`, `Falconer_Angular_AngularCountMean`, `Falconer_Angular_AngularDroppedMaximum`, `Falconer_Angular_AngularProductEnergyIntegral`, `Falconer_Angular_CircleAngularBins`, `Falconer_Angular_CircleLocalIntegral`, `Falconer_Angular_CircleMaskCoordinates`, `Falconer_Angular_CircleRotation`, `Falconer_Angular_CircleStationaryPartition`, `Falconer_Angular_CircleTests`, `Falconer_Angular_CompactCircleResidual`, `Falconer_Angular_GraphAngleCharts`, `Falconer_Angular_GraphRotatedWeights`, `Falconer_Angular_InverseCircleArcLength`, `Falconer_Angular_InverseCircleAssembly`, `Falconer_Angular_InverseStationaryOperators`, `Falconer_Angular_InverseStationaryRemainder`, `Falconer_Angular_NormalizedStationaryJet`, `Falconer_Angular_RetainedAngularFailure`, `Falconer_Angular_RotatedConeKernel`, `Falconer_Angular_RotatedInverseCircle`, `Falconer_Angular_SignedStationaryExpansion`, `Falconer_Angular_SignedStationaryJet`, `Falconer_Angular_SignedStationaryRadial`, `Falconer_Angular_SingleStationaryRadial`, `Falconer_Angular_SmoothAngleMask`, `Falconer_Angular_StationaryChartIntegral`, `Falconer_Angular_StationaryJetOperators`, `Falconer_Estimates_ActualOuterMasks`, `Falconer_Estimates_DistanceEligibleIndices`, `Falconer_Estimates_DistanceMatrixData`, `Falconer_Estimates_IntermediateProfiles`, `Falconer_Estimates_OuterChildProfileBound`, `Falconer_Estimates_OuterMaskFailure`, `Falconer_Estimates_ProductMatrix`, `Falconer_Estimates_ProfileInterpolation`, `Falconer_Estimates_RootLeibniz`, `Falconer_Estimates_RootSpatialTerms`, `Falconer_Estimates_SelectedDistanceAssembly`, `Falconer_Estimates_SignedConvolution`, `Falconer_Estimates_SmoothConvolution`, `Falconer_Estimates_SpatialAnchorMasks`, `Falconer_Estimates_SpatialLeibnizSubpower`, `Falconer_Fourier_GoodSupportedKernelMajorant`, `Falconer_Fourier_GraphFourSymbolDerivatives`, `Falconer_Fourier_KernelFourierIdentity`, `Falconer_Fourier_MeasureKernelConvolution`, `Falconer_Fourier_RootPairSymbols`, `Falconer_Fourier_SmoothKernel`, `Falconer_Frostman_GeometricCapacity`, `Falconer_Geometry_CellwiseDistanceForm`, `Falconer_Geometry_DyadicClasses`, `Falconer_Geometry_DyadicPacking`, `Falconer_Geometry_InactiveBinGeometry`, `Falconer_Geometry_InactiveBinScales`, `Falconer_Geometry_RootPatchGeometry`, `Falconer_Geometry_SelectedBinAmplitude`, `Falconer_Graphs_ActualProductDegrees`, `Falconer_Graphs_DistancePairDegree`, `Falconer_Graphs_DistanceSupportedGraph`, `Falconer_Graphs_EligibleProductGraphSum`, `Falconer_Graphs_Energy`, `Falconer_Graphs_FiberSlice`, `Falconer_Graphs_GraphAlgebraicDirections`, `Falconer_Graphs_GraphAmplitudeDerivatives`, `Falconer_Graphs_GraphAmplitudeRepresentative`, `Falconer_Graphs_GraphAmplitudeSupport`, `Falconer_Graphs_GraphCartesianSubstitution`, `Falconer_Graphs_GraphChartVariation`, `Falconer_Graphs_GraphCompleteWeightSupport`, `Falconer_Graphs_GraphConeCutoff`, `Falconer_Graphs_GraphCoordinateInverse`, `Falconer_Graphs_GraphDirectionStability`, `Falconer_Graphs_GraphFixedCutoffs`, `Falconer_Graphs_GraphFourTransformExpansion`, `Falconer_Graphs_GraphGeometry`, `Falconer_Graphs_GraphGlobalChart`, `Falconer_Graphs_GraphGlobalDomain`, `Falconer_Graphs_GraphLiftJacobian`, `Falconer_Graphs_GraphNonedgeIndexCount`, `Falconer_Graphs_GraphNonedgeIntegralErrors`, `Falconer_Graphs_GraphOriginalFubini`, `Falconer_Graphs_GraphOriginalNonedgePower`, `Falconer_Graphs_GraphParentDiameter`, `Falconer_Graphs_GraphPolarAnnulus`, `Falconer_Graphs_GraphPolarJacobian`, `Falconer_Graphs_GraphRetainedEdges`, `Falconer_Graphs_GraphSignChart`, `Falconer_Graphs_GraphSignPartition`, `Falconer_Graphs_GraphSignSupports`, `Falconer_Graphs_GraphTransportIntegrability`, `Falconer_Graphs_GraphWeightDerivatives`, `Falconer_Graphs_ParentGraphEnergy`, `Falconer_Graphs_ParentGraphIndices`, `Falconer_Graphs_ParentRetainedEnergy`, `Falconer_Graphs_ProductGraphIndices`, `Falconer_Graphs_ProductPairDegree`, `Falconer_Graphs_SourceSpatialEnergy`, `Falconer_Measures_ExtendedDensityNorm`, `Falconer_Measures_FourSpatialPairMeasure`, `Falconer_Radial_ProjectionEnergy`, `Falconer_Radial_RadialDistanceError`, `Falconer_Radial_RadialFailureMass`, `Falconer_Radial_RadialTestEnergy`, `Falconer_Radial_RadialTestNorm`, `Falconer_Radial_RadialTonelli`, `Falconer_Recursion_DescriptorMasks`, `Falconer_Recursion_ParentBinFamily`, `Falconer_Recursion_ParentBinSelection`, `Falconer_Recursion_ParentCellGeometry`, `Falconer_Recursion_PolicyInteriorInterval`, `Falconer_Recursion_PrefixCounting`, `Falconer_Recursion_RetainedPairMasks`, `Falconer_Shells_ShellFrequencyEnergy`, `Falconer_Shells_ShellKernels`, `Falconer_Shells_ShellSummability`, `Falconer_Shells_Shells`, `Falconer_Shells_SmoothShellPartition`, `Falconer_Shells_TwoRootCandidates`, `Falconer_Shells_TwoRootClassMixture`, `Falconer_Shells_TwoRootMasks`.
--
--   **Imports.** It imports the published bundle `Def_PlanarFalconer`; the bundles `OAIQ038F000` and `OAIQ038F001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF_shell`, `OAI.PlanarFalconer.PositiveDistanceData.uniform_weighted_high_shell_inverse`, `OAI.PlanarFalconer.exists_normalized_root_setup`, `OAI.PlanarFalconer.finite_radial_testNorm_integral`, `OAI.PlanarFalconer.original_distance_graph_integral_bound`, `OAI.PlanarFalconer.original_product_graph_integral_bound`, `OAI.PlanarFalconer.rotated_inverse_circle_power`, `OAI.PlanarFalconer.sourceGraphFourTransform_pointIntegral`, `OAI.PlanarFalconer.two_root_has_shell_approximations`, `OAI.PlanarFalconer.two_root_restored_removed_mass_bound`, `OAI.PlanarFalconer.uniform_actual_comparable_shell_rebin`, `OAI.PlanarFalconer.uniform_actual_distance_HF_graph`, `OAI.PlanarFalconer.uniform_actual_distance_degrees`, `OAI.PlanarFalconer.uniform_actual_graph_amplitude_E`, `OAI.PlanarFalconer.uniform_actual_graph_nonedge_power`, `OAI.PlanarFalconer.uniform_actual_product_H_graph`, `OAI.PlanarFalconer.uniform_actual_retained_distance_graph`, `OAI.PlanarFalconer.uniform_parent_discarded_F`, `OAI.PlanarFalconer.uniform_regularized_original_graph_removal`, `OAI.PlanarFalconer.uniform_root_weighted_inverse` and `OAI.PlanarFalconer.uniform_rotated_actual_inactive_bins`; the proofs of `OAI.PlanarFalconer.PositiveDistanceData.inverseOrderForm_shell`, `OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF_measurable`, `OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF_shell`, `OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_parent_bound`, `OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_profile_error`, `OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_band`, `OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_high_shell`, `OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_inverse_supremum`, `OAI.PlanarFalconer.PositiveDistanceData.uniform_weighted_high_shell_inverse`, `OAI.PlanarFalconer.RootShellData.inverseOrderForm_shell`, `OAI.PlanarFalconer.RootShellData.mainF_shell`, `OAI.PlanarFalconer.RootShellData.uniform_parent_bound`, `OAI.PlanarFalconer.actual_angular_near_fixed`, `OAI.PlanarFalconer.actual_profile_regularization`, `OAI.PlanarFalconer.exists_normalized_root_setup`, `OAI.PlanarFalconer.finite_radial_testNorm_integral`, `OAI.PlanarFalconer.full_circle_stationary_expansion`, `OAI.PlanarFalconer.mainTarget_proved`, `OAI.PlanarFalconer.original_distance_graph_integral_bound`, `OAI.PlanarFalconer.original_product_graph_integral_bound`, `OAI.PlanarFalconer.rotated_inverse_circle_power`, `OAI.PlanarFalconer.sourceGraphFourTransform_pointIntegral`, `OAI.PlanarFalconer.source_angular_direct`, `OAI.PlanarFalconer.source_positive_distance_suffix`, `OAI.PlanarFalconer.stationary_product_radial_bound`, `OAI.PlanarFalconer.two_root_has_shell_approximations`, `OAI.PlanarFalconer.two_root_restored_removed_mass_bound`, `OAI.PlanarFalconer.uniform_actual_angular_recursion_bound`, `OAI.PlanarFalconer.uniform_actual_comparable_far_error`, `OAI.PlanarFalconer.uniform_actual_comparable_shell_rebin`, `OAI.PlanarFalconer.uniform_actual_distance_HF_graph`, `OAI.PlanarFalconer.uniform_actual_distance_degrees`, `OAI.PlanarFalconer.uniform_actual_distance_equation12`, `OAI.PlanarFalconer.uniform_actual_distance_low_band`, `OAI.PlanarFalconer.uniform_actual_far_radial_error`, `OAI.PlanarFalconer.uniform_actual_far_source_equation24`, `OAI.PlanarFalconer.uniform_actual_far_stationary_integrable`, `OAI.PlanarFalconer.uniform_actual_far_stationary_reduction`, `OAI.PlanarFalconer.uniform_actual_four_approximant_good`, `OAI.PlanarFalconer.uniform_actual_graph_amplitude_E`, `OAI.PlanarFalconer.uniform_actual_graph_nonedge_power`, `OAI.PlanarFalconer.uniform_actual_noncomparable_radial_either`, `OAI.PlanarFalconer.uniform_actual_product_H_graph`, `OAI.PlanarFalconer.uniform_actual_product_estimate`, `OAI.PlanarFalconer.uniform_actual_recursive_profile`, `OAI.PlanarFalconer.uniform_actual_retained_distance_graph`, `OAI.PlanarFalconer.uniform_actual_single_stationary_kernel`, `OAI.PlanarFalconer.uniform_actual_suffix_local_bins`, `OAI.PlanarFalconer.uniform_independent_class_equation27`, `OAI.PlanarFalconer.uniform_outer_root_graph_bound`, `OAI.PlanarFalconer.uniform_parent_discarded_F`, `OAI.PlanarFalconer.uniform_recursive_energy_rules`, `OAI.PlanarFalconer.uniform_regularized_original_graph_removal`, `OAI.PlanarFalconer.uniform_root_fourier_error`, `OAI.PlanarFalconer.uniform_root_weighted_inverse` and `OAI.PlanarFalconer.uniform_rotated_actual_inactive_bins`.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/MeasureTheory/Falconer at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F000
import Definitions.Def_OAIQ038F001

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SmoothAngleMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function ContinuousLinearMap
open scoped Convolution Topology ContDiff

theorem thickenedIndicator_bounds (G : Set ℝ) (η x : ℝ) :
    0 ≤ thickenedIndicator G η x ∧ thickenedIndicator G η x ≤ 1 := by
  classical
  by_cases h : x ∈ thickening (2*η) G <;> simp [thickenedIndicator,h]

theorem smoothAngleMask_bounds (G : Set ℝ) (η : ℝ) (hη : 0 < η) (x : ℝ) :
    0 ≤ smoothAngleMask G η hη x ∧ smoothAngleMask G η hη x ≤ 1 := by
  have hp := (angleBump η hη).nonneg_normed (μ := volume)
  constructor
  · apply integral_nonneg
    intro t
    exact mul_nonneg (hp t) (thickenedIndicator_bounds G η (x-t)).1
  · have he : (((angleBump η hη).normed volume) ⋆[lsmul ℝ ℝ,volume] (fun _ : ℝ => (1:ℝ))) x = 1 :=
      (angleBump η hη).normed_convolution_eq_right (fun _ _ => rfl)
    rw [← he]
    apply convolution_mono_right_of_nonneg _ hp (fun t => (thickenedIndicator_bounds G η t).2) (fun _ => zero_le_one)
    simpa only [ConvolutionExistsAt,lsmul_apply,smul_eq_mul,mul_one] using
      (angleBump η hη).integrable_normed (μ := volume)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Frostman_GeometricCapacity
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable def occupiedCapacity (E : Set Plane) (s : ℝ) (Q : DyadicSquare) : ℝ := by
  classical
  exact if (E ∩ Q.carrier).Nonempty then Q.side ^ s else 0

noncomputable def geometricTree (E : Set Plane) (s : ℝ) (Q : DyadicSquare) :
    ℕ → CapacityTree
  | 0 => .leaf (occupiedCapacity E s Q)
  | K+1 => .node (occupiedCapacity E s Q)
      (geometricTree E s (Q.child false false) K)
      (geometricTree E s (Q.child false true) K)
      (geometricTree E s (Q.child true false) K)
      (geometricTree E s (Q.child true true) K)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicPacking
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable def cellsMeeting (Q : DyadicSquare) (n : ℕ) (x : Plane) (r : ℝ) :
    Finset (List (Bool × Bool)) := by
  classical
  exact (dyadicPaths n).filter fun p =>
    ((Q.descendant p).carrier ∩ ball x r).Nonempty

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicClasses
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem leafUnion_measurable (Q : DyadicSquare) (L : Finset (List (Bool × Bool))) :
    MeasurableSet (leafUnion Q L) :=
  Finset.measurableSet_biUnion _ (fun p _ => (Q.descendant p).measurable)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PrefixCounting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def prefixFiber (C : Finset CellPath) (a : ℕ) (P : CellPath) : Finset CellPath := by
  classical
  exact C.filter fun q => q.take a = P

noncomputable def prefixChildren (C : Finset CellPath) (a b : ℕ) (P : CellPath) :
    Finset CellPath := (prefixFiber C a P).image (List.take b)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProfileInterpolation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def regularizedProfile (L : Finset CellPath) (F : CellPath → List ℕ)
    (N B K : ℕ) (p : CellPath) : ℝ → ℝ :=
  finiteRampProfile (fun i => (blockDepth N B i : ℝ)) (fun i => blockSlope L F N B i p) K

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_IntermediateProfiles
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal

noncomputable def sourceProfile (Q : DyadicSquare) (μ : Measure Plane)
    (N B : ℕ) (p : CellPath) : ℝ → ℝ :=
  regularizedProfile (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) N B (N/B+1) p

noncomputable def sourceClass (Q : DyadicSquare) (μ : Measure Plane)
    (N B : ℕ) (p : CellPath) : Measure Plane :=
  normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
    (regularizationLabel Q μ N B p)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def graphDirection (z : ℝ) (ξ : Plane) : Plane :=
  (Real.sqrt (1+z^2))⁻¹ • (ξ+z • quarterTurn ξ)

theorem norm_quarterTurn_add (z : ℝ) (v : Plane) :
    ‖quarterTurn v + z • v‖ = Real.sqrt (1+z^2) * ‖v‖ := by
  have hs : 0 ≤ 1+z^2 := by positivity
  have hsq := Real.sq_sqrt hs
  have hv := EuclideanSpace.real_norm_sq_eq v
  have hw := EuclideanSpace.real_norm_sq_eq (quarterTurn v + z • v)
  simp [Fin.sum_univ_two,quarterTurn] at hv hw
  have he : ‖quarterTurn v + z • v‖^2 = (Real.sqrt (1+z^2)*‖v‖)^2 := by
    calc
      _ = (-v 1+z*v 0)^2+(v 0+z*v 1)^2 := hw
      _ = _ := by rw [mul_pow,hsq,hv]; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp he

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_Energy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable def rieszPotential (μ : Measure Plane) (u : ℝ) (x : Plane) : ℝ≥0∞ :=
  ∫⁻ y, (edist x y)^(-u) ∂μ

noncomputable def rieszEnergy (μ : Measure Plane) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, rieszPotential μ u x ∂μ

noncomputable def energyMajorantTerm (x : Plane) (u : ℝ) (n : ℕ) : Plane → ℝ≥0∞ :=
  (ball x (2*energyScale n)).indicator
    (fun _ => ENNReal.ofReal ((energyScale n/2)^(-u)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_ProjectionEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable def planePhase (z : Plane) : ℝ :=
  Complex.arg (Complex.orthonormalBasisOneI.repr.symm z)

noncomputable def projectedMeasure (μ : Measure Plane) (θ : ℝ) : Measure ℝ :=
  μ.map (sourceProjection θ)

instance projectedMeasure_finite (μ : Measure Plane) [IsFiniteMeasure μ] (θ : ℝ) :
    IsFiniteMeasure (projectedMeasure μ θ) := by unfold projectedMeasure; infer_instance

noncomputable def differenceEnergyMeasure (μ : Measure Plane) (t : ℝ) : Measure (Plane × Plane) :=
  (μ.prod μ).withDensity (fun z => (edist z.1 z.2)^(-t))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_FiberSlice
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace

noncomputable def sourceDensityMeasure (a : Plane → ℝ) : Measure Plane :=
  volume.withDensity (fun x => ENNReal.ofReal (a x))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SmoothKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Convolution

noncomputable def sourceBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : Plane) where
  rIn := ε/2
  rOut := ε
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

noncomputable def sourceMollifier (ε : ℝ) (hε : 0 < ε) : Plane → ℝ :=
  (sourceBump ε hε).normed volume

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialTestNorm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

instance sourceArcLength_finite : IsFiniteMeasure sourceArcLength := by
  unfold sourceArcLength
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def sourceTestNorm (q : ℝ) (γ : Measure UnitCircle) : ℝ≥0∞ :=
  ⨆ (F : BoundedContinuousFunction UnitCircle ℝ)
    (_ : eLpNorm F (ENNReal.ofReal q) sourceArcLength ≤ 1),
      ENNReal.ofReal ‖∫ ω, F ω ∂γ‖

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularCountMean
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def stripHitBound (W : ℝ) (z : Plane) : ℝ≥0∞ :=
  if z=0 then ENNReal.ofReal (2*Real.pi)
  else ENNReal.ofReal (4*Real.pi*min 1 (W/‖z‖))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngleCoordinateTests
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceDirection_dist_le (θ φ : ℝ) :
    dist (sourceDirection θ) (sourceDirection φ) ≤ 2*dist θ φ := by
  unfold sourceDirection
  rw [LinearIsometryEquiv.dist_map]
  have hc := Real.lipschitzWith_cos.dist_le_mul θ φ
  have hs := Real.lipschitzWith_sin.dist_le_mul θ φ
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hc hs
  rw [dist_eq_norm]
  have hh := Complex.norm_le_abs_re_add_abs_im
    ((Real.cos θ+Real.sin θ*Complex.I)-(Real.cos φ+Real.sin φ*Complex.I))
  simp only [Complex.sub_re,Complex.add_re,Complex.mul_I_re,Complex.ofReal_re,
    Complex.ofReal_im,neg_zero,add_zero,Complex.sub_im,Complex.add_im,
    Complex.mul_I_im,zero_add] at hh
  exact hh.trans (by rw [Real.dist_eq]; linarith)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngleMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceTestMask_bounds (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) (θ : ℝ) :
    0 ≤ sourceTestMask G d hd θ ∧ sourceTestMask G d hd θ ≤ 1 := smoothAngleMask_bounds _ _ _ _

noncomputable def sourceParallelMask (N : ℕ) (sig : ℝ) (J i : ℕ)
    (Q : DyadicSquare) (ρ : Measure Plane) (g p : ℕ) (P : CellPath) (T : ℝ) : ℝ → ℝ :=
  sourceTestMask (parallelGoodSet Q ρ g p P (sourceAngularWidth N sig J i p) T)
    (sourceAngularRadius N sig (p-g)) (sourceAngularRadius_pos _ _ _)

noncomputable def sourceProjectionMask (N : ℕ) (sig : ℝ) (J i : ℕ)
    (Q : DyadicSquare) (ρ : Measure Plane) (p u : ℕ) (P : CellPath) (T : ℝ) : ℝ → ℝ :=
  sourceTestMask (projectionGoodSet Q ρ p u P (sourceAngularWidth N sig J i u) T)
    (sourceAngularRadius N sig (u-p)) (sourceAngularRadius_pos _ _ _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_ExtendedDensityNorm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable def sourceDensityNorm (p : ℝ) (γ : Measure UnitCircle) : ℝ≥0∞ := by
  classical
  exact if γ ≪ sourceArcLength then
    eLpNorm (fun x => (γ.rnDeriv sourceArcLength x).toReal) (ENNReal.ofReal p) sourceArcLength
  else ∞

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleTests
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

instance unitCircle_compactSpace : CompactSpace UnitCircle := by
  apply isCompact_iff_compactSpace.mp
  have he : (fun z : Plane => ‖z‖ = 1) = (sphere (0 : Plane) 1 : Set Plane) := by
    funext z
    simp [Metric.sphere, dist_zero_right, Set.ofPred]
  rw [he]
  exact isCompact_sphere (0 : Plane) 1

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleMaskCoordinates
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceAngle_sourceUnitDirection (θ : ℝ) :
    sourceAngle (sourceUnitDirection θ) =
      Complex.arg ((Real.cos θ:ℂ)+(Real.sin θ:ℂ)*Complex.I) := by
  simp only [sourceAngle,sourceUnitDirection,sourceDirection,LinearIsometryEquiv.symm_apply_apply]

theorem circleTestMask_bounds (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) (dir : UnitCircle) :
    0 ≤ circleTestMask G d hd dir ∧ circleTestMask G d hd dir ≤ 1 := sourceTestMask_bounds _ _ _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SpatialAnchorMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem spatialAnchorMask_eq (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) {P : CellPath}
    (hP : P ∈ occupiedAnchorPaths Q ρ n) {x : Plane} (hx : x ∈ (Q.descendant P).carrier)
    (dir : UnitCircle) : spatialAnchorMask Q ρ n G d hd x dir = circleTestMask (G P) d hd dir := by
  classical
  unfold spatialAnchorMask
  rw [Finset.sum_eq_single P]
  · simp [hx]
  · intro c hc hcP
    have hdj := Q.descendants_disjoint hQ
      (((mem_dyadicPaths n c).mp (Finset.mem_filter.mp hc).1).trans
        ((mem_dyadicPaths n P).mp (Finset.mem_filter.mp hP).1).symm) hcP
    have hx' : x ∉ (Q.descendant c).carrier := fun h => Set.disjoint_left.mp hdj h hx
    simp [hx']
  · intro h; exact (h hP).elim

theorem spatialAnchorMask_zero (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) {x : Plane}
    (hx : ∀ P ∈ occupiedAnchorPaths Q ρ n, x ∉ (Q.descendant P).carrier) (dir : UnitCircle) :
    spatialAnchorMask Q ρ n G d hd x dir = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro P hP
  simp [hx P hP]

theorem spatialAnchorMask_bounds (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) (dir : UnitCircle) :
    0 ≤ spatialAnchorMask Q ρ n G d hd x dir ∧ spatialAnchorMask Q ρ n G d hd x dir ≤ 1 := by
  by_cases hx : ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier
  · obtain ⟨P,hP,hx⟩ := hx
    rw [spatialAnchorMask_eq Q hQ ρ n G d hd hP hx]
    exact circleTestMask_bounds _ _ _ _
  · push Not at hx
    rw [spatialAnchorMask_zero Q ρ n G d hd hx]
    norm_num

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PolicyInteriorInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def policyRepresentatives (A : ℕ → ℝ) (N q : ℕ) : Finset ℕ :=
  (Finset.range (N/q+1)).image (policyRepresentative A N q)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_DescriptorMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem descriptorSpatialMask_bounds (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) (dir : UnitCircle) :
    0 ≤ descriptorSpatialMask Q ρ m N lam sig J i b x dir ∧
      descriptorSpatialMask Q ρ m N lam sig J i b x dir ≤ 1 := spatialAnchorMask_bounds Q hQ _ _ _ _ _ _ _

theorem descriptorListMask_bounds (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (S : Finset PolicyDescriptor) (x : Plane) (dir : UnitCircle) :
    0 ≤ descriptorListMask Q ρ m N lam sig J i S x dir ∧
      descriptorListMask Q ρ m N lam sig J i S x dir ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun b _ => (descriptorSpatialMask_bounds Q hQ ρ m N lam sig J i b x dir).1)
  · exact Finset.prod_le_one (fun b _ => (descriptorSpatialMask_bounds Q hQ ρ m N lam sig J i b x dir).1)
      (fun b _ => (descriptorSpatialMask_bounds Q hQ ρ m N lam sig J i b x dir).2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryChartIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def localizedCircleIntegral (Λ : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ θ in stationarySineInverse (-1)..stationarySineInverse 1,
    Complex.exp (Complex.I*(Λ:ℂ)*(Real.cos θ:ℂ)) *
      (stationaryCutoff (stationarySineChart θ) : ℂ) * f θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleStationaryPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

noncomputable def circleStationaryResidual (θ : ℝ) : ℝ :=
  1-stationaryCutoff (stationarySineChart θ)-stationaryCutoff (stationaryCosineChart θ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleLocalIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def circlePositivePiece (Λ : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ *
    (stationaryCutoff (stationarySineChart θ):ℂ)*f θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleAngularBins
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

 theorem circleAngularBin_support_radius {n : ℕ} (hn : 0 < n) (j : ℕ) :
    Function.support (circleAngularBin n j) ⊆
      closedBall (sourceUnitDirection (2*Real.pi/(n : ℝ)*(j : ℝ))) (4*Real.pi/(n : ℝ)) := by
  intro dir hdir
  let θ := sourceAngle dir
  let t := (n : ℝ)/(2*Real.pi)*θ
  obtain ⟨k,hk,hnear⟩ := angularBinSelection_witness _ t hdir
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hπ : (0 : ℝ) < 2*Real.pi := by positivity
  have hid : θ-2*Real.pi/(n : ℝ)*(k : ℝ) = (2*Real.pi/(n : ℝ))*(t-k) := by
    dsimp [t]
    field_simp
  have hdist : dist θ (2*Real.pi/(n : ℝ)*(k : ℝ)) ≤ 2*Real.pi/(n : ℝ) := by
    rw [Real.dist_eq, hid, abs_mul, abs_of_pos (by positivity)]
    simpa using mul_le_mul_of_nonneg_left hnear (by positivity : 0 ≤ 2*Real.pi/(n : ℝ))
  change dist dir _ ≤ _
  rw [← angularBin_center_residue hn j k hk, ← sourceUnitDirection_sourceAngle dir]
  change dist (sourceDirection θ) (sourceDirection _) ≤ _
  apply (sourceDirection_dist_le θ _).trans
  calc
    _ ≤ 2*(2*Real.pi/(n : ℝ)) := mul_le_mul_of_nonneg_left hdist (by norm_num)
    _ = _ := by ring

 theorem circleAngularBin_tsupport_radius {n : ℕ} (hn : 0 < n) (j : ℕ) :
    tsupport (circleAngularBin n j) ⊆
      closedBall (sourceUnitDirection (2*Real.pi/(n : ℝ)*(j : ℝ))) (4*Real.pi/(n : ℝ)) :=
  closure_minimal (circleAngularBin_support_radius hn j) isClosed_closedBall

 theorem circleAngularBin_diameter {n : ℕ} (hn : 0 < n) (j : ℕ)
    {dir φ : UnitCircle} (hdir : dir ∈ tsupport (circleAngularBin n j))
    (hφ : φ ∈ tsupport (circleAngularBin n j)) : dist dir φ ≤ 8*Real.pi/(n : ℝ) := by
  have h1 := circleAngularBin_tsupport_radius hn j hdir
  have h2 := circleAngularBin_tsupport_radius hn j hφ
  have hd := dist_triangle dir (sourceUnitDirection (2*Real.pi/(n : ℝ)*(j : ℝ))) φ
  rw [dist_comm (sourceUnitDirection (2*Real.pi/(n : ℝ)*(j : ℝ))) φ] at hd
  exact hd.trans ((add_le_add h1 h2).trans_eq (by ring))

 theorem circleAngularBin_scale_diameter {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 2*Real.pi)
    (j : ℕ) {dir φ : UnitCircle}
    (hdir : dir ∈ tsupport (circleAngularBin (angularBinCount δ) j))
    (hφ : φ ∈ tsupport (circleAngularBin (angularBinCount δ) j)) : dist dir φ ≤ 4*δ := by
  have hb := (angularBinCount_bounds hδ hcap).1
  apply (circleAngularBin_diameter (angularBinCount_pos hδ) j hdir hφ).trans
  calc
    _ = 4*(2*Real.pi/(angularBinCount δ : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryJetOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

noncomputable def stationaryJet (n : ℕ) (f : ℝ → ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), (n.choose k:ℂ) *
    iteratedDeriv k (fun u => (stationaryWeight u : ℂ)) 0 *
      ∑ c : OrderedFinpartition (n-k),
        ((∏ j, iteratedDeriv (c.partSize j) extendedStationaryInverse 0 : ℝ):ℂ) *
          iteratedDeriv c.length f 0

noncomputable def directStationaryOperator (j : ℕ) (f : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ((Real.sqrt (2*Real.pi):ℂ) * Complex.exp (-(Real.pi:ℂ)/4*Complex.I)) *
    (((j.factorial:ℝ)⁻¹:ℝ):ℂ) * (-Complex.I/2)^j *
      stationaryJet (2*j) (fun u => f (u+θ))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseStationaryOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

noncomputable def inverseStationaryOperator (j : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (inverseStationaryExpr j).apply f

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CompactCircleResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff Topology

noncomputable def compactCircleResidual : ℝ → ℝ :=
  (Ioo (-Real.pi) Real.pi).indicator circleStationaryResidual

noncomputable def circleResidualAmplitude (f : ℝ → ℂ) (θ : ℝ) : ℂ :=
  (compactCircleResidual θ : ℂ)*f θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseStationaryRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

noncomputable def inverseDirectExpansion (q j : ℕ) (Λ : ℝ) (f : ℝ → ℂ) : ℂ :=
  Complex.exp (Complex.I*(Λ:ℂ)) * ((Λ^(-1/2:ℝ):ℝ):ℂ) *
    ∑ h ∈ Finset.range (q+1), ((Λ⁻¹:ℝ):ℂ)^h *
      directStationaryOperator h (inverseStationaryOperator j f) 0

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseCircleAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

noncomputable def inverseCircleIntegral (n : ℕ) (Λ : ℝ) (ψ f : ℝ → ℂ) : ℂ :=
  ((Λ^(1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1), ((Λ⁻¹:ℝ):ℂ)^j *
    ∫ θ in (-Real.pi)..Real.pi,
      cosineOscillator Λ θ * (ψ θ * inverseStationaryOperator j f θ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RotatedInverseCircle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

noncomputable def rotatedInverseCircleIntegral (n : ℕ) (Λ θ₀ : ℝ)
    (ψ f : ℝ → ℂ) : ℂ :=
  ((Λ^(1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1), ((Λ⁻¹:ℝ):ℂ)^j *
    ∫ θ in (-Real.pi)..Real.pi,
      cosineOscillator Λ (θ-θ₀) * (ψ θ * inverseStationaryOperator j f θ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseCircleArcLength
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

noncomputable def inverseCircleOperator (j : ℕ) (b : UnitCircle → ℂ) : UnitCircle → ℂ :=
  fun dir => inverseStationaryOperator j (fun θ => b (sourceUnitDirection θ)) (sourceAngle dir)

theorem inner_sourceDirection (θ φ : ℝ) :
    inner ℝ (sourceDirection θ) (sourceDirection φ) = Real.cos (θ-φ) := by
  unfold sourceDirection
  rw [LinearIsometryEquiv.inner_map_map]
  simp [Complex.inner, Real.cos_sub, -Complex.ofReal_cos, -Complex.ofReal_sin, mul_comm]

noncomputable def sourceInverseCircleIntegral (n : ℕ) (r : ℝ) (Δ : Plane)
    (ψ b : UnitCircle → ℂ) : ℂ :=
  (((r*‖Δ‖)^(1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1), (((r*‖Δ‖)⁻¹:ℝ):ℂ)^j *
    ∫ dir, Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (dir:Plane) Δ:ℂ)) *
      (ψ dir * inverseCircleOperator j b dir) ∂sourceArcLength

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_SelectedBinAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def selectedBinAmplitude (δ : ℝ) (S : Finset ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun θ => ((∑ k ∈ S, periodicAngularBin (angularBinCount δ) k θ : ℝ) : ℂ)*f θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphDirectionStability
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

 theorem normalized_vector_dist_le (u v : Plane) (hu : u ≠ 0) (hv : v ≠ 0) :
    dist (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) ≤ 2*dist u v/‖u‖ := by
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hid : ‖u‖⁻¹ • u - ‖v‖⁻¹ • v =
      ‖u‖⁻¹ • (u-v) + (‖u‖⁻¹-‖v‖⁻¹) • v := by
    rw [smul_sub, sub_smul]
    abel
  have hcoeff : |‖u‖⁻¹-‖v‖⁻¹| * ‖v‖ = |‖v‖-‖u‖|/‖u‖ := by
    rw [show ‖u‖⁻¹-‖v‖⁻¹ = (‖v‖-‖u‖)/(‖u‖*‖v‖) by
      field_simp [ne_of_gt hu0, ne_of_gt hv0],
      abs_div, abs_mul, abs_of_pos hu0, abs_of_pos hv0]
    field_simp [ne_of_gt hu0, ne_of_gt hv0]
  rw [dist_eq_norm, hid]
  calc
    _ ≤ ‖‖u‖⁻¹ • (u-v)‖ + ‖(‖u‖⁻¹-‖v‖⁻¹) • v‖ := norm_add_le _ _
    _ = ‖u-v‖/‖u‖ + |‖v‖-‖u‖|/‖u‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hu0), hcoeff]
      ring
    _ ≤ ‖u-v‖/‖u‖ + ‖u-v‖/‖u‖ := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right _ hu0.le
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le v u
    _ = _ := by rw [dist_eq_norm]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_InactiveBinGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set Metric
open scoped ContDiff Topology

noncomputable def inactiveAngularLabels (n : ℕ) (e : UnitCircle) (radius : ℝ) : Finset ℕ :=
  (Finset.range n).filter (fun j => ¬ AngularBinActive n j e radius)

theorem sourceUnitDirection_dist_sq (θ φ : ℝ) :
    dist (sourceUnitDirection θ) (sourceUnitDirection φ)^2 = 2-2*Real.cos (θ-φ) := by
  change dist (sourceDirection θ) (sourceDirection φ)^2 = _
  rw [dist_eq_norm, norm_sub_sq_real, norm_sourceDirection, norm_sourceDirection, inner_sourceDirection]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleRotation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem periodic_sourceAngle_value {E : Type*} {f : ℝ → E}
    (hf : Function.Periodic f (2*Real.pi)) (θ : ℝ) :
    f (sourceAngle (sourceUnitDirection θ)) = f θ := by
  rw [sourceAngle_sourceUnitDirection]
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  have hp := hf.int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋
  simpa only [mul_comm, add_comm] using hp θ

theorem sourceCircleRotate_comp (axis θ : ℝ) :
    sourceCircleRotate axis (sourceUnitDirection θ) = sourceUnitDirection (θ+axis) := by
  exact periodic_sourceAngle_value (f := fun t => sourceUnitDirection (t+axis))
    (fun t => by simpa only [add_right_comm] using sourceUnitDirection_periodic (t+axis)) θ

theorem sourceCircleRotate_dist (axis : ℝ) (dir eta : UnitCircle) :
    dist (sourceCircleRotate axis dir) (sourceCircleRotate axis eta) = dist dir eta := by
  rw [← sourceUnitDirection_sourceAngle dir, ← sourceUnitDirection_sourceAngle eta,
    sourceCircleRotate_comp, sourceCircleRotate_comp]
  have h₁ := sourceUnitDirection_dist_sq (sourceAngle dir+axis) (sourceAngle eta+axis)
  have h₂ := sourceUnitDirection_dist_sq (sourceAngle dir) (sourceAngle eta)
  rw [show sourceAngle dir+axis-(sourceAngle eta+axis) = sourceAngle dir-sourceAngle eta by ring] at h₁
  nlinarith [dist_nonneg (x := sourceUnitDirection (sourceAngle dir+axis))
    (y := sourceUnitDirection (sourceAngle eta+axis)),
    dist_nonneg (x := sourceUnitDirection (sourceAngle dir)) (y := sourceUnitDirection (sourceAngle eta))]

theorem sourceCircleRotate_isometry (axis : ℝ) : Isometry (sourceCircleRotate axis) :=
  Isometry.of_dist_eq (sourceCircleRotate_dist axis)

theorem sourceCircleRotate_add (a b : ℝ) (dir : UnitCircle) :
    sourceCircleRotate a (sourceCircleRotate b dir) = sourceCircleRotate (b+a) dir := by
  change sourceCircleRotate a (sourceUnitDirection (sourceAngle dir+b)) = _
  rw [sourceCircleRotate_comp]
  simp only [sourceCircleRotate, add_assoc]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphConeCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff

theorem graphConeCutoff_support : tsupport graphConeCutoff ⊆ Icc (-1/5 : ℝ) (1/5) := by
  have hb : tsupport (graphConeBump : ℝ → ℝ) = Icc (-1/5 : ℝ) (1/5) := by
    rw [ContDiffBump.tsupport_eq, Real.closedBall_eq_Icc]
    norm_num [graphConeBump]
  exact (tsupport_comp_subset (g := Complex.ofReal) rfl (graphConeBump : ℝ → ℝ)).trans hb.subset

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RotatedConeKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable def rotatedBinSelection (n : ℕ) (S : Finset ℕ) (axis : ℝ)
    (dir : UnitCircle) : ℂ :=
  ((∑ j ∈ S, circleAngularBin n j (sourceCircleRotate (-axis) dir) : ℝ) : ℂ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphCoordinateInverse
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem graph_quarterTurn_norm (v : Plane) : ‖quarterTurn v‖ = ‖v‖ := by
  simpa using norm_quarterTurn_add 0 v

theorem orthogonal_vector_quarterTurn (d w : Plane) (hw : w ≠ 0)
    (hd : planeDot d w = 0) :
    d = (planeDot d (quarterTurn w)/‖w‖^2) • quarterTurn w := by
  have hn : ‖w‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  have hs := EuclideanSpace.real_norm_sq_eq w
  simp only [Fin.sum_univ_two] at hs
  have hm0 : (d 0*w 0+d 1*w 1)*w 0 = 0 := by rw [← planeDot,hd,zero_mul]
  have hm1 : (d 0*w 0+d 1*w 1)*w 1 = 0 := by rw [← planeDot,hd,zero_mul]
  ext i
  fin_cases i <;> simp [quarterTurn, planeDot] <;> field_simp <;> rw [hs] <;> nlinarith

theorem graph_chart_difference (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : u+v ≠ 0) : u-v = graphChartZ u v • quarterTurn (u+v) := by
  apply orthogonal_vector_quarterTurn _ _ hw
  have hs₁ := EuclideanSpace.real_norm_sq_eq u
  have hs₂ := EuclideanSpace.real_norm_sq_eq v
  rw [hu] at hs₁
  rw [hv] at hs₂
  simp only [Fin.sum_univ_two] at hs₁ hs₂
  simp [planeDot]
  nlinarith

theorem graph_chart_radius_identity (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : u+v ≠ 0) : ‖u+v‖*Real.sqrt (1+(graphChartZ u v)^2) = 2 := by
  have hpar : ‖u+v‖^2+‖u-v‖^2 = 4 := by
    rw [norm_add_sq_real, norm_sub_sq_real, hu, hv]
    ring
  have hd := congrArg (fun w : Plane => ‖w‖^2) (graph_chart_difference u v hu hv hw)
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, graph_quarterTurn_norm] at hd
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1+(graphChartZ u v)^2)
  have he : (‖u+v‖*Real.sqrt (1+(graphChartZ u v)^2))^2 = (2:ℝ)^2 := by
    rw [mul_pow,hs]
    nlinarith
  exact (sq_eq_sq₀ (by positivity) (by norm_num)).mp he

theorem graph_chart_nondegenerate_bound (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hchart : 1/2 ≤ ‖u+v‖) :
    Real.sqrt (1+(graphChartZ u v)^2) ≤ 4 ∧ |graphChartZ u v| ≤ 4 := by
  have hw : u+v ≠ 0 := norm_pos_iff.mp (by linarith)
  have he := graph_chart_radius_identity u v hu hv hw
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1+(graphChartZ u v)^2)
  have hspos := Real.sqrt_nonneg (1+(graphChartZ u v)^2)
  have hb : Real.sqrt (1+(graphChartZ u v)^2) ≤ 4 := by nlinarith
  exact ⟨hb, by nlinarith [sq_abs (graphChartZ u v),abs_nonneg (graphChartZ u v)]⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphSignChart
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem circle_sign_norm (s : ℝ) (hs : s = 1 ∨ s = -1) (ω : UnitCircle) :
    ‖s • (ω:Plane)‖ = 1 := by
  rcases hs with rfl | rfl <;> simp [ω.property]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphSignPartition
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

theorem circleGraphSignPlus_tsupport :
    tsupport circleGraphSignPlus ⊆ {p | 1 ≤ ‖(p.1:Plane)+(p.2:Plane)‖} := by
  apply closure_minimal
  · intro p hp
    have h : 0 < (‖(p.1:Plane)+(p.2:Plane)‖^2-1)/2 :=
      not_le.mp (fun hn => hp (Real.smoothTransition.zero_of_nonpos hn))
    change 1 ≤ ‖(p.1:Plane)+(p.2:Plane)‖
    nlinarith [norm_nonneg ((p.1:Plane)+(p.2:Plane))]
  · exact isClosed_le continuous_const (by fun_prop)

theorem circleGraphSignMinus_tsupport :
    tsupport circleGraphSignMinus ⊆ {p | 1 ≤ ‖(p.1:Plane)-(p.2:Plane)‖} := by
  apply closure_minimal
  · intro p hp
    have h : (‖(p.1:Plane)+(p.2:Plane)‖^2-1)/2 < 1 := by
      apply not_le.mp
      intro hn
      apply hp
      change 1-Real.smoothTransition _ = 0
      rw [Real.smoothTransition.one_of_one_le hn, sub_self]
    have he : ‖(p.1:Plane)+(p.2:Plane)‖^2+‖(p.1:Plane)-(p.2:Plane)‖^2 = 4 := by
      rw [norm_add_sq_real, norm_sub_sq_real, p.1.property, p.2.property]
      ring
    change 1 ≤ ‖(p.1:Plane)-(p.2:Plane)‖
    nlinarith [norm_nonneg ((p.1:Plane)-(p.2:Plane))]
  · exact isClosed_le continuous_const (by fun_prop)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphLiftJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

noncomputable def graphLiftMap (p : GraphLiftSpace) : GraphLiftSpace :=
  ![p 0*Real.sqrt (1+(p 2)^2)/2, p 1+Real.arctan (p 2), p 1-Real.arctan (p 2)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphPolarJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def graphPolarMap (p : GraphLiftSpace) : GraphLiftSpace :=
  ![p 0*Real.cos (p 1), p 0*Real.sin (p 1), p 2]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphCartesianSubstitution
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def graphCartesianFrequency (x : GraphLiftSpace) : Plane := WithLp.toLp 2 ![x 0,x 1]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphPolarAnnulus
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def graphPlaneEquiv : (ℝ × ℝ) ≃ᵐ Plane :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphGlobalChart
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def graphPlaneAngle (η : Plane) : ℝ :=
  (polarCoord (graphPlaneEquiv.symm η)).2

def graphGlobalSlice (a b z : ℝ) : Set Plane :=
  graphPlaneEquiv '' (polarCoord.symm ''
    graphPolarRectangle (2*a/Real.sqrt (1+z^2)) (2*b/Real.sqrt (1+z^2)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphGlobalDomain
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def graphPlaneSlit : Set Plane := graphPlaneEquiv.symm ⁻¹' polarCoord.source

def graphGlobalAnnulus (a b z : ℝ) : Set Plane :=
  {η | ‖η‖*Real.sqrt (1+z^2)/2 ∈ Ioo a b}

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphChartVariation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem quarterTurn_sub_p1 (u v : Plane) : quarterTurn (u-v) = quarterTurn u-quarterTurn v := by
  ext i
  fin_cases i <;> simp [quarterTurn]
  ring

theorem graphChartZ_dist_le (u v u' v' : Plane)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hu' : ‖u'‖ = 1) (hv' : ‖v'‖ = 1)
    (hw : 1/2 ≤ ‖u+v‖) (hw' : 1/2 ≤ ‖u'+v'‖) :
    |graphChartZ u v-graphChartZ u' v'| ≤ 10*(dist u u'+dist v v') := by
  have hd := graph_chart_difference u v hu hv (norm_pos_iff.mp (by linarith))
  have hd' := graph_chart_difference u' v' hu' hv' (norm_pos_iff.mp (by linarith))
  have hz := (graph_chart_nondegenerate_bound u' v' hu' hv' hw').2
  have hsum : ‖(u+v)-(u'+v')‖ ≤ dist u u'+dist v v' := by
    simpa only [dist_eq_norm] using dist_add_add_le u v u' v'
  have hdiff : ‖(u-v)-(u'-v')‖ ≤ dist u u'+dist v v' := by
    simpa only [dist_eq_norm] using dist_sub_sub_le u v u' v'
  have he : (graphChartZ u v-graphChartZ u' v') • quarterTurn (u+v) =
      ((u-v)-(u'-v'))-graphChartZ u' v' • quarterTurn ((u+v)-(u'+v')) := by
    rw [quarterTurn_sub_p1, smul_sub, hd, hd', sub_smul]
    abel
  have hn : |graphChartZ u v-graphChartZ u' v'| *‖u+v‖ ≤
      5*(dist u u'+dist v v') := by
    calc
      _ = ‖(graphChartZ u v-graphChartZ u' v') • quarterTurn (u+v)‖ := by
        rw [norm_smul, Real.norm_eq_abs, graph_quarterTurn_norm]
      _ ≤ ‖(u-v)-(u'-v')‖+‖graphChartZ u' v' • quarterTurn ((u+v)-(u'+v'))‖ :=
        he ▸ norm_sub_le _ _
      _ = ‖(u-v)-(u'-v')‖+|graphChartZ u' v'| *‖(u+v)-(u'+v')‖ := by
        rw [norm_smul, Real.norm_eq_abs, graph_quarterTurn_norm]
      _ ≤ (dist u u'+dist v v')+4*(dist u u'+dist v v') :=
        add_le_add hdiff (mul_le_mul hz hsum (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  nlinarith [abs_nonneg (graphChartZ u v-graphChartZ u' v')]

theorem graphChartAxis_dist_le (u v u' v' : Plane)
    (hw : 1/2 ≤ ‖u+v‖) (hw' : 1/2 ≤ ‖u'+v'‖) :
    dist (graphChartAxis u v) (graphChartAxis u' v') ≤ 4*(dist u u'+dist v v') := by
  have hw0 : 0 < ‖u+v‖ := by linarith
  have hh := normalized_vector_dist_le (u+v) (u'+v') (norm_pos_iff.mp hw0)
    (norm_pos_iff.mp (by linarith))
  have hb : dist (u+v) (u'+v') ≤ dist u u'+dist v v' := dist_add_add_le _ _ _ _
  apply hh.trans
  apply (div_le_iff₀ hw0).mpr
  have ht : 0 ≤ dist u u'+dist v v' := by positivity
  nlinarith

theorem graph_sign_bin_pair_variation (s : ℝ) (hs : s = 1 ∨ s = -1)
    (p q : UnitCircle × UnitCircle)
    (hp : 1/2 ≤ ‖(p.1:Plane)+s • (p.2:Plane)‖)
    (hq : 1/2 ≤ ‖(q.1:Plane)+s • (q.2:Plane)‖) :
    |graphChartZ (p.1:Plane) (s • (p.2:Plane))-graphChartZ (q.1:Plane) (s • (q.2:Plane))|+
      dist (graphChartAxis (p.1:Plane) (s • (p.2:Plane)))
        (graphChartAxis (q.1:Plane) (s • (q.2:Plane))) ≤
      14*(dist p.1 q.1+dist p.2 q.2) := by
  have hz := graphChartZ_dist_le _ _ _ _ p.1.property (circle_sign_norm s hs p.2)
    q.1.property (circle_sign_norm s hs q.2) hp hq
  have ha := graphChartAxis_dist_le (p.1:Plane) (s • (p.2:Plane))
    (q.1:Plane) (s • (q.2:Plane)) hp hq
  have hd : dist (s • (p.2:Plane)) (s • (q.2:Plane)) = dist p.2 q.2 := by
    change dist (s • (p.2:Plane)) (s • (q.2:Plane)) = dist (p.2:Plane) (q.2:Plane)
    rcases hs with rfl | rfl <;> simp
  rw [hd] at hz ha
  change _ ≤ 10*(dist p.1 q.1+dist p.2 q.2) at hz
  change _ ≤ 4*(dist p.1 q.1+dist p.2 q.2) at ha
  linarith

theorem graph_complete_support_representative (s δ : ℝ) (hs : s = 1 ∨ s = -1)
    (S : Set (UnitCircle × UnitCircle)) (hS : S.Nonempty)
    (hchart : ∀ p ∈ S, 1/2 ≤ ‖(p.1:Plane)+s • (p.2:Plane)‖)
    (hbin : ∀ p ∈ S, ∀ q ∈ S, dist p.1 q.1 ≤ δ ∧ dist p.2 q.2 ≤ δ) :
    ∃ q ∈ S, ∀ p ∈ S,
      |graphChartZ (p.1:Plane) (s • (p.2:Plane))-graphChartZ (q.1:Plane) (s • (q.2:Plane))|+
      dist (graphChartAxis (p.1:Plane) (s • (p.2:Plane)))
        (graphChartAxis (q.1:Plane) (s • (q.2:Plane))) ≤ 28*δ := by
  obtain ⟨q,hq⟩ := hS
  refine ⟨q,hq,?_⟩
  intro p hp
  have hv := graph_sign_bin_pair_variation s hs p q (hchart p hp) (hchart q hq)
  have hb := hbin p hp q hq
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphSignSupports
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem sourceConeCircle_tsupport_dist (axis : ℝ) :
    tsupport (sourceConeCircle axis) ⊆ {dir | dist dir (sourceUnitDirection axis) ≤ 2/5} := by
  apply closure_minimal
  · intro dir hdir
    have ht := graphConeCutoff_support (subset_closure hdir)
    change sourceAngle (sourceCircleRotate (-axis) dir) ∈ Icc (-1/5:ℝ) (1/5) at ht
    have hd := sourceDirection_dist_le (sourceAngle (sourceCircleRotate (-axis) dir)) 0
    have hb : dist (sourceCircleRotate (-axis) dir) (sourceUnitDirection 0) ≤ 2/5 := by
      rw [← sourceUnitDirection_sourceAngle (sourceCircleRotate (-axis) dir)]
      change dist (sourceDirection _) (sourceDirection 0) ≤ _
      rw [Real.dist_eq, sub_zero] at hd
      have ha : |sourceAngle (sourceCircleRotate (-axis) dir)| ≤ 1/5 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      linarith
    have he := sourceCircleRotate_dist axis (sourceCircleRotate (-axis) dir) (sourceUnitDirection 0)
    simp only [sourceCircleRotate_add, neg_add_cancel, sourceCircleRotate_zero,
      sourceCircleRotate_comp, zero_add] at he
    change dist dir (sourceUnitDirection axis) ≤ 2/5
    rwa [he]
  · exact isClosed_le (by fun_prop) continuous_const

theorem sourceConeCircle_plus_nondegenerate (axis : ℝ) (u v : UnitCircle)
    (hu : u ∈ tsupport (sourceConeCircle axis)) (hv : v ∈ tsupport (sourceConeCircle axis)) :
    6/5 ≤ ‖(u:Plane)+(v:Plane)‖ := by
  have hu' := sourceConeCircle_tsupport_dist axis hu
  have hv' := sourceConeCircle_tsupport_dist axis hv
  let a : Plane := sourceDirection axis
  have ha : ‖a+a‖ = 2 := by
    rw [← two_smul ℝ a, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<2)]
    simp [a, norm_sourceDirection]
  have hd := dist_add_add_le a a (u:Plane) (v:Plane)
  have hn := norm_sub_norm_le (a+a) ((u:Plane)+(v:Plane))
  rw [ha] at hn
  rw [dist_eq_norm] at hd
  change dist (u:Plane) a ≤ 2/5 at hu'
  change dist (v:Plane) a ≤ 2/5 at hv'
  rw [dist_comm (u:Plane) a] at hu'
  rw [dist_comm (v:Plane) a] at hv'
  linarith

noncomputable def circleGraphSignWeight (s : ℝ) : UnitCircle × UnitCircle → ℝ :=
  if s = 1 then circleGraphSignPlus else circleGraphSignMinus

theorem circleGraphSignWeight_nondegenerate (s : ℝ) (hs : s = 1 ∨ s = -1)
    {p : UnitCircle × UnitCircle} (hp : p ∈ tsupport (circleGraphSignWeight s)) :
    1/2 ≤ ‖(p.1:Plane)+s • (p.2:Plane)‖ := by
  rcases hs with rfl | rfl
  · simp only [circleGraphSignWeight] at hp
    simpa only [one_smul] using (show (1/2:ℝ) ≤ 1 by norm_num).trans
      (circleGraphSignPlus_tsupport hp)
  · norm_num [circleGraphSignWeight] at hp
    have hh := circleGraphSignMinus_tsupport hp
    simpa only [neg_one_smul, ← sub_eq_add_neg] using
      (show (1/2:ℝ) ≤ 1 by norm_num).trans hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphTransportIntegrability
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def graphTransport (F : ℝ → UnitCircle → UnitCircle → ℂ)
    (Ψ : ℝ → ℝ) (R axis : ℝ) (p : ℝ × Plane) : ℂ :=
  (‖p.2‖*Real.sqrt (1+p.1^2))⁻¹ •
    (Ψ (‖p.2‖*Real.sqrt (1+p.1^2)/2) •
      F (R*(‖p.2‖*Real.sqrt (1+p.1^2)/2))
        (sourceUnitDirection (graphPlaneAngle p.2+Real.arctan p.1))
        (sourceUnitDirection (graphPlaneAngle p.2-Real.arctan p.1+axis)))

def graphTransportBox : Set (ℝ × Plane) := Icc (-4) 4 ×ˢ Metric.closedBall 0 8

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphOriginalFubini
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def graphOriginalKernel (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (Ψ : ℝ → ℝ) (R : ℝ)
    (p : ℝ × (UnitCircle × UnitCircle)) (x : Fin 4 → Plane) : ℂ :=
  Ψ (p.1/R) • graphFourKernel b W x p.1 p.2.1 p.2.2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialDistanceError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def sourceRadialSquareEnergy (a v : ℝ) (Ψ : ℝ → ℝ) (F : ℝ → ℂ) : ℝ :=
  (2:ℝ)^(2*(v-a)) * ∫ r, ‖F r‖^2 ∂sourceAngularShellMeasure v Ψ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphFourTransformExpansion
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def sourceGraphFourTransform
    (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (r : ℝ) (u v : UnitCircle) : ℂ :=
  W (u,v) *
    (sourceAngularTransform (ρ 0) (X 0) (M 0) (b 0) r u *
      conj (sourceAngularTransform (ρ 1) (X 1) (M 1) (b 1) r u)) *
    (sourceAngularTransform (ρ 2) (X 2) (M 2) (b 2) r v *
      conj (sourceAngularTransform (ρ 3) (X 3) (M 3) (b 3) r v))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularProductEnergyIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable def sourceRealAngularMoment (U : ℝ × UnitCircle → ℂ) (r : ℝ) : ℝ :=
  ∫ u, ‖U (r,u)‖^2 ∂sourceArcLength

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_InactiveBinScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def graphAngularScale (N : ℕ) (sig t c₀ : ℝ) : ℝ :=
  min c₀ (graphUncappedAngularScale N sig t)

theorem graphUncappedAngularScale_pos (N : ℕ) (sig t : ℝ) :
    0 < graphUncappedAngularScale N sig t := by
  unfold graphUncappedAngularScale
  positivity

theorem graphAngularScale_pos (N : ℕ) (sig t : ℝ) {c₀ : ℝ} (hc : 0 < c₀) :
    0 < graphAngularScale N sig t c₀ := lt_min hc (graphUncappedAngularScale_pos N sig t)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphAlgebraicDirections
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff

noncomputable def graphNormalizedAxis (η : Plane) : Plane := ‖η‖⁻¹ • η

noncomputable def graphAlgebraicDirection (plus : Bool) (p : Plane × ℝ) : Plane :=
  (Real.sqrt (1+p.2^2))⁻¹ •
    (graphNormalizedAxis p.1 + (if plus then p.2 else -p.2) • quarterTurn (graphNormalizedAxis p.1))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_GraphAngleCharts
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric Filter
open scoped ContDiff Topology

noncomputable def graphComplexCoordinate (η : Plane) : ℂ :=
  Complex.orthonormalBasisOneI.repr.symm η

noncomputable def graphAngleCoordinate (positive plus : Bool) (p : Plane × ℝ) : ℝ :=
  Complex.arg (if positive then graphComplexCoordinate p.1 else -graphComplexCoordinate p.1) +
    (if plus then Real.arctan p.2 else -Real.arctan p.2)

noncomputable def graphAngularPullback (f : ℝ → ℂ) (plus : Bool) (c : ℝ)
    (p : Plane × ℝ) : ℂ := f (graphPlaneAngle p.1 +
      (if plus then Real.arctan p.2 else -Real.arctan p.2)+c)

def graphAngleCompact (positive : Bool) : Set (Plane × ℝ) :=
  (closedBall 0 8 ∩ {p | 1/8 ≤ ‖p.1‖}) ∩
    {p | 0 ≤ (if positive then graphComplexCoordinate p.1 else -graphComplexCoordinate p.1).re}

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_GraphRotatedWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem graphRotatedDistanceWeight_eq (axis : ℝ) (n j k : ℕ) (u v : UnitCircle) :
    graphRotatedDistanceWeight axis n j k (u,v) =
      (sourceConeCircle axis u * rotatedBinSelection n {j} axis u) *
        conj (sourceConeCircle axis v * rotatedBinSelection n {k} axis v) := by
  simp only [graphRotatedDistanceWeight, graphDistanceWeight, graphBinWeight,
    rotatedBinSelection, Finset.sum_singleton, sourceConeCircle,
    neg_zero, sourceCircleRotate_zero, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_GraphFourSymbolDerivatives
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def graphFourSymbolProduct (F : Fin 4 → (Plane × ℝ) → ℂ)
    (p : Plane × ℝ) : ℂ := (F 0 p * conj (F 1 p)) * (F 2 p * conj (F 3 p))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphFixedCutoffs
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff ComplexConjugate

noncomputable def graphFixedSign (plus : Bool) (p : Plane × ℝ) : ℂ :=
  if plus then (graphSignPlus (graphAlgebraicDirection true p, graphAlgebraicDirection false p) : ℝ)
  else (graphSignMinus (graphAlgebraicDirection true p, -graphAlgebraicDirection false p) : ℝ)

noncomputable def graphShellJacobian (Ψ : ℝ → ℝ) (p : Plane × ℝ) : ℂ :=
  ((‖p.1‖*Real.sqrt (1+p.2^2))⁻¹ * Ψ (‖p.1‖*Real.sqrt (1+p.2^2)/2) : ℝ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphWeightDerivatives
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff ComplexConjugate

noncomputable def graphBinPullback (δ : ℝ) (S : Finset ℕ) (plus : Bool) (c : ℝ) :
    (Plane × ℝ) → ℂ := graphAngularPullback
      (fun θ => ((∑ k ∈ S, periodicAngularBin (angularBinCount δ) k θ : ℝ):ℂ)) plus c

noncomputable def graphConePullback (plus : Bool) (c : ℝ) : (Plane × ℝ) → ℂ :=
  graphAngularPullback (fun θ => sourceConeCircle 0 (sourceUnitDirection θ)) plus c

noncomputable def graphWeightPullback (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    (p : Plane × ℝ) : ℂ := graphSourceWeight distance plus axis (angularBinCount δ) j k
      (sourceUnitDirection (graphPlaneAngle p.1+Real.arctan p.2),
        sourceUnitDirection (graphPlaneAngle p.1-Real.arctan p.2+graphSourceChartAxis distance plus))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphAmplitudeDerivatives
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def graphAmplitudePullback (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    (Ψ : ℝ → ℝ) (p : Plane × ℝ) : ℂ :=
  graphShellJacobian Ψ p * graphFourAmplitude b
    (graphSourceWeight distance plus axis (angularBinCount δ) j k) x
      (sourceUnitDirection (graphPlaneAngle p.1+Real.arctan p.2))
      (sourceUnitDirection (graphPlaneAngle p.1-Real.arctan p.2+graphSourceChartAxis distance plus))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphNonedgeIndexCount
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

def graphCellQuadIndices (p : ℕ) : Finset GraphCellQuadIndex :=
  ((dyadicPaths p).product (dyadicPaths p)).product ((dyadicPaths p).product (dyadicPaths p))

def graphNonedgeIndices (p n : ℕ) : Finset GraphNonedgeIndex :=
  (graphCellQuadIndices p).product (((Finset.range n).product (Finset.range n)).product Finset.univ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphParentDiameter
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

def graphSlotParent (distance : Bool) (X Y : DyadicSquare) (l : Fin 4) : DyadicSquare :=
  if distance then (if l = 0 ∨ l = 3 then X else Y) else (if l.val < 2 then X else Y)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ProductGraphIndices
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def sourceProductRelativeIndices (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (n m : ℕ) : Finset GraphNonedgeIndex :=
  (((occupiedAnchorPaths X ρ n) ×ˢ (occupiedAnchorPaths X ρ n)) ×ˢ
    ((occupiedAnchorPaths Y ν n) ×ˢ (occupiedAnchorPaths Y ν n))) ×ˢ
      (((Finset.range m) ×ˢ (Finset.range m)) ×ˢ Finset.univ)

def sourceProductGraphIndex (A B : CellPath) (e : GraphNonedgeIndex) : GraphNonedgeIndex :=
  (((A++e.1.1.1,A++e.1.1.2),(B++e.1.2.1,B++e.1.2.2)),e.2)

noncomputable def sourceProductGraphIndices (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (n m : ℕ) (A B : CellPath) : Finset GraphNonedgeIndex := by
  classical
  exact (sourceProductRelativeIndices X Y ρ ν n m).image (sourceProductGraphIndex A B)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphAmplitudeSupport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology

def graphAmplitudeCompact : Set (Plane × ℝ) :=
  (closedBall 0 8 ×ˢ Icc (-4) 4) ∩ {p | 1/8 ≤ ‖p.1‖}

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphCompleteWeightSupport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ComplexConjugate

theorem graphSourceSign_cases (distance plus : Bool) :
    graphSourceSign distance plus = 1 ∨ graphSourceSign distance plus = -1 := by
  cases distance <;> cases plus <;> norm_num [graphSourceSign]

noncomputable def graphSourceBinDirection (distance : Bool) (axis : ℝ)
    (u : UnitCircle) : UnitCircle := if distance then sourceCircleRotate (-axis) u else u

theorem graphSourceBinDirection_continuous (distance : Bool) (axis : ℝ) :
    Continuous (graphSourceBinDirection distance axis) := by
  cases distance
  · exact continuous_id
  · exact (sourceCircleRotate_isometry (-axis)).continuous

theorem graphSourceBinDirection_dist (distance : Bool) (axis : ℝ) (u v : UnitCircle) :
    dist (graphSourceBinDirection distance axis u) (graphSourceBinDirection distance axis v) = dist u v := by
  cases distance
  · rfl
  · exact sourceCircleRotate_dist (-axis) u v

theorem graphSourceWeight_support_bins (distance plus : Bool) (axis : ℝ) (n j k : ℕ) :
    tsupport (graphSourceWeight distance plus axis n j k) ⊆
      {p | graphSourceBinDirection distance axis p.1 ∈ tsupport (circleAngularBin n j) ∧
        graphSourceBinDirection distance axis p.2 ∈ tsupport (circleAngularBin n k)} := by
  apply closure_minimal
  · intro p hp
    constructor
    · apply subset_closure
      intro hz
      apply hp
      cases distance <;> simp_all [graphSourceWeight, graphSourceBinDirection,
        graphRotatedDistanceWeight, graphDistanceWeight, graphProductWeight, graphBinWeight]
    · apply subset_closure
      intro hz
      apply hp
      cases distance <;> simp_all [graphSourceWeight, graphSourceBinDirection,
        graphRotatedDistanceWeight, graphDistanceWeight, graphProductWeight, graphBinWeight]
  · exact (isClosed_closure.preimage ((graphSourceBinDirection_continuous distance axis).comp continuous_fst)).inter
      (isClosed_closure.preimage ((graphSourceBinDirection_continuous distance axis).comp continuous_snd))

theorem graphSourceWeight_support_nondegenerate (distance plus : Bool) (axis : ℝ) (n j k : ℕ) :
    tsupport (graphSourceWeight distance plus axis n j k) ⊆
      {p | 1/2 ≤ ‖(p.1:Plane)+graphSourceSign distance plus • (p.2:Plane)‖} := by
  apply closure_minimal
  · intro p hp
    cases distance
    · have hs : p ∈ tsupport (circleGraphSignWeight (graphSourceSign false plus)) := by
        apply subset_closure
        intro hz
        apply hp
        cases plus <;> simp_all [graphSourceWeight, graphSourceSign, circleGraphSignWeight, graphProductWeight]
        norm_num at hz
        exact hp.2 hz
      exact circleGraphSignWeight_nondegenerate _ (graphSourceSign_cases false plus) hs
    · have he : graphRotatedDistanceWeight axis n j k p ≠ 0 := hp
      rw [graphRotatedDistanceWeight_eq] at he
      have hu : sourceConeCircle axis p.1 ≠ 0 := by intro hz; exact he (by simp [hz])
      have hv : sourceConeCircle axis p.2 ≠ 0 := by intro hz; exact he (by simp [hz])
      have hb := sourceConeCircle_plus_nondegenerate axis p.1 p.2 (subset_closure hu) (subset_closure hv)
      change 1/2 ≤ ‖(p.1:Plane)+(1:ℝ) • (p.2:Plane)‖
      simpa only [one_smul] using (by norm_num : (1/2:ℝ) ≤ 6/5).trans hb
  · exact isClosed_le continuous_const (by fun_prop)

theorem graphSourceWeight_complete_representative {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 2*Real.pi)
    (distance plus : Bool) (axis : ℝ) (j k : ℕ)
    (hS : (tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty) :
    ∃ q ∈ tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k),
      ∀ p ∈ tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k),
      |graphChartZ (p.1:Plane) (graphSourceSign distance plus • (p.2:Plane))-
        graphChartZ (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))|+
      dist (graphChartAxis (p.1:Plane) (graphSourceSign distance plus • (p.2:Plane)))
        (graphChartAxis (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))) ≤ 112*δ := by
  have hb := graphSourceWeight_support_bins distance plus axis (angularBinCount δ) j k
  have hv := graph_complete_support_representative _ (4*δ) (graphSourceSign_cases distance plus) _ hS
    (graphSourceWeight_support_nondegenerate distance plus axis (angularBinCount δ) j k) ?_
  · convert hv using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  · intro p hp q hq
    have h₁ := circleAngularBin_scale_diameter hδ hcap j (hb hp).1 (hb hq).1
    have h₂ := circleAngularBin_scale_diameter hδ hcap k (hb hp).2 (hb hq).2
    rw [graphSourceBinDirection_dist] at h₁ h₂
    exact ⟨h₁,h₂⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphAmplitudeRepresentative
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

noncomputable def graphSourceEndpoints (distance plus : Bool) (p : Plane × ℝ) : UnitCircle × UnitCircle :=
  (sourceUnitDirection (graphPlaneAngle p.1+Real.arctan p.2),
    sourceUnitDirection (graphPlaneAngle p.1-Real.arctan p.2+graphSourceChartAxis distance plus))

theorem graphSourceRepresentative_exists {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 2*Real.pi)
    (distance plus : Bool) (axis : ℝ) (j k : ℕ)
    (hS : (tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty) :
    ∃ q, GraphSourceRepresentative distance plus axis δ j k q :=
  graphSourceWeight_complete_representative hδ hcap distance plus axis j k hS

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphNonedgeIntegralErrors
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def graphPointIntegral (f : Plane × ℝ → ℂ) (v s : ℝ) (x y : Plane) : ℂ :=
  ∫ z : ℝ, ∫ η : Plane, Complex.exp (Complex.I*Complex.ofReal
    ((2:ℝ)^v*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphOriginalNonedgePower
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def graphOriginalTerm (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane)
    (M : Fin 4 → ℝ) (b : Fin 4 → Plane → UnitCircle → ℂ)
    (distance plus : Bool) (axis δ v : ℝ) (j k : ℕ) (Ψ : ℝ → ℝ) : ℂ :=
  ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
    sourceGraphFourTransform ρ X M b (graphSourceWeight distance plus axis (angularBinCount δ) j k) r u w
      ∂sourceArcLength ∂sourceArcLength)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_EligibleProductGraphSum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def graphProductEligibleIndices (I : Finset GraphNonedgeIndex)
    (ρ : Fin 4 → Measure Plane) (Q : Fin 4 → DyadicSquare)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (m : ℕ) : Finset GraphNonedgeIndex := by
  classical
  exact I.filter (GraphProductIndexEligible ρ Q b m)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphRetainedEdges
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

noncomputable def graphChosenRepresentative {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 2*Real.pi)
    (distance plus : Bool) (axis : ℝ) (j k : ℕ) : UnitCircle × UnitCircle := by
  classical
  exact if hs : (tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty then
    Classical.choose (graphSourceRepresentative_exists hδ hcap distance plus axis j k hs)
  else (sourceUnitDirection 0,sourceUnitDirection 0)

noncomputable def graphRetainedIndices (I : Finset GraphNonedgeIndex) (N : ℕ) (sig p : ℝ)
    (distance : Bool) (Q : Fin 4 → DyadicSquare) (q : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle) :
    Finset GraphNonedgeIndex := by
  classical
  exact I.filter (fun e => GraphRetainedEdge N sig p distance e.2.2 (graphQuadCells Q e.1) (q e.2))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ProductPairDegree
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def productPairCells (Q₁ Q₂ : DyadicSquare) (row col : CellPath × CellPath) :
    Fin 4 → DyadicSquare :=
  ![Q₁.descendant row.1,Q₁.descendant col.1,Q₂.descendant row.2,Q₂.descendant col.2]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProductMatrix
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def sourceRetainedProductIndices
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (A B : CellPath) (a n m N : ℕ) (sig : ℝ)
    (rep : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle) : Finset GraphNonedgeIndex :=
  graphProductEligibleIndices
    (graphRetainedIndices
      (sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B)
      N sig (a+n) false ![Q₁,Q₁,Q₂,Q₂] rep)
    ![ρ,ρ,ν,ν] ![Q₁,Q₁,Q₂,Q₂] ![β,β,γ,γ] m

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ActualProductDegrees
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def graphSupportedProductIndices (I : Finset GraphNonedgeIndex) (θ : ℝ) :
    Finset GraphNonedgeIndex := by
  classical
  exact I.filter (fun e => (tsupport (graphSourceWeight false e.2.2 0
    (angularBinCount θ) e.2.1.1 e.2.1.2)).Nonempty)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDroppedMaximum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

noncomputable def remainingAngularEnergy
    {ι : Fin 2 → Type} (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
    (k : ∀ l, ι l → ℕ) (Q : Fin 2 → DyadicSquare) (ρ : Fin 2 → Measure Plane)
    (mass : Fin 2 → ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Fin 2 → Plane → ℂ)
    (M₁ M₂ p v : ℝ) (Ψ : ℝ → ℝ) (row : CellPath × CellPath) : ℝ≥0∞ :=
  sourceAngularH p v Ψ
    (fun z => sourceAngularTransform (ρ 0) ((Q 0).descendant row.1).carrier M₁
      (inheritedCircleSymbol ((S 0).filter (fun c => row.1.length < descriptorAnchor (d 0 c)))
        (d 0) (k 0) (Q 0) (ρ 0) (mass 0) N lam sig J i (h 0)) z.1 z.2)
    (fun z => sourceAngularTransform (ρ 1) ((Q 1).descendant row.2).carrier M₂
      (inheritedCircleSymbol ((S 1).filter (fun c => row.2.length < descriptorAnchor (d 1 c)))
        (d 1) (k 1) (Q 1) (ρ 1) (mass 1) N lam sig J i (h 1)) z.1 z.2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_NormalizedStationaryJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

noncomputable def normalizedStationaryJet (j : ℕ) (f : ℝ → ℂ) (θ Λ : ℝ) : ℂ :=
  ((Λ⁻¹:ℝ):ℂ)^j * directStationaryOperator j f θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualOuterMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem outerEndpointMask_bounds (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig kap : ℝ) (c : ℕ) (x : Plane) (dir : UnitCircle) :
    0 ≤ outerEndpointMask Q ρ m N lam sig kap c x dir ∧
      outerEndpointMask Q ρ m N lam sig kap c x dir ≤ 1 := descriptorListMask_bounds Q hQ _ _ _ _ _ _ _ _ _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialFailureMass
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable def radialFailure (S : Plane → Set UnitCircle) : Set (Plane × Plane) :=
  {z | sourceRadialUnit z.1 z.2 ∈ S z.1}

instance weightedDistance_finite (π : Measure (Plane × Plane))
    [IsFiniteMeasure (π.withDensity distanceWeight)] : IsFiniteMeasure (weightedDistance π) := by
  unfold weightedDistance
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_RetainedPairMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem measurableSet_actualClassDomain (Q : DyadicSquare) (μ : Measure Plane) (N B : ℕ) (T : List ℕ) :
    MeasurableSet (actualClassDomain Q μ N B T) := leafUnion_measurable _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_OuterMaskFailure
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def outerAllEntryFailure (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig kap : ℝ) (x : Plane) : Set UnitCircle :=
  ⋃ c ∈ Finset.range (N+1), {dir | outerEndpointMask Q ρ m N lam sig kap c x dir ≠ 1}

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RetainedAngularFailure
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def retainedAngularFailure (Q : DyadicSquare) (μ : Measure Plane)
    (m : List ℕ → ℝ → ℝ) (N B : ℕ) (lam sig kap : ℝ) (x : Plane) : Set UnitCircle :=
  ⋃ T ∈ retainedClassLabels Q μ N B (ENNReal.ofReal (((2:ℝ)^N)^(-lam))),
    {dir | x ∈ actualClassDomain Q μ N B T ∧
      dir ∈ outerAllEntryFailure Q (actualClassMeasure Q μ N B T) (m T) N lam sig kap x}

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SignedStationaryJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff ComplexConjugate

noncomputable def signedStationaryJet (plus : Bool) (j : ℕ) (f : ℝ → ℂ) (θ Λ : ℝ) : ℂ :=
  if plus then normalizedStationaryJet j f θ Λ else
    conj (normalizedStationaryJet j (fun t => conj (f (t+Real.pi))) θ Λ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SignedStationaryRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def signedStationaryRadialCoefficient (Ψ : ℝ → ℝ) (plus₁ plus₂ : Bool)
    (j k : ℕ) (f g : ℝ → ℂ) (θ φ A B : ℝ) (s : ℝ) : ℂ :=
  (((A^(-1/2:ℝ)*B^(-1/2:ℝ):ℝ):ℂ) *
    (signedStationaryJet plus₁ j f θ A * signedStationaryJet plus₂ k g φ B)) *
      radialStationaryProfile Ψ (-((j:ℝ)+(k:ℝ)+1)) s

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SignedStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff ComplexConjugate

noncomputable def signedStationaryTerm (plus : Bool) (j : ℕ) (f : ℝ → ℂ) (Λ : ℝ) : ℂ :=
  Complex.exp (Complex.I*((stationarySign plus*Λ:ℝ):ℂ)) *
    ((Λ^(-1/2:ℝ):ℝ):ℂ) * signedStationaryJet plus j f 0 Λ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SingleStationaryRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def singleStationaryRadialCoefficient (Ψ : ℝ → ℝ) (plus : Bool)
    (j : ℕ) (f : ℝ → ℂ) (θ A : ℝ) (s : ℝ) : ℂ :=
  (((A^(-1/2:ℝ):ℝ):ℂ) * signedStationaryJet plus j f θ A) *
    radialStationaryProfile Ψ (-((j:ℝ)+1/2)) s

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_CellwiseDistanceForm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def sourceCellwiseDistanceF (P Q : DyadicSquare)
    (ρ ν : Measure Plane) (n m : ℕ) (M₁ M₂ : ℝ)
    (ψ : CellPath → CellPath → UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (r : ℝ) : ℂ :=
  ∑ A ∈ occupiedAnchorPaths P ρ n, ∑ B ∈ occupiedAnchorPaths Q ν m,
    sourceDistanceF (ψ A B)
      (fun z => sourceAngularTransform ρ (P.descendant A).carrier M₁ b₁ z.1 z.2)
      (fun z => sourceAngularTransform ν (Q.descendant B).carrier M₂ b₂ z.1 z.2) r

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ParentCellGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

noncomputable def sourceCenteredCellDirection (X Y P Q : DyadicSquare) : UnitCircle :=
  sourceCircleRotate (-sourceParentAxis X Y) (sourceRadialUnit Q.center P.center)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ParentBinSelection
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def sourceParentInactiveSelection (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (A B : CellPath) : UnitCircle → ℂ :=
  rotatedBinSelection (angularBinCount (graphUncappedAngularScale N sig t))
    (inactiveAngularLabels (angularBinCount (graphUncappedAngularScale N sig t))
      (sourceCenteredCellDirection X Y (X.descendant A) (Y.descendant B))
      (3*graphUncappedAngularScale N sig t)) (sourceParentAxis X Y)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ParentRetainedEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def sourceParentDiscardedF (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (ρ ν : Measure Plane) (n : ℕ)
    (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) : ℝ → ℂ :=
  sourceCellwiseDistanceF X Y ρ ν n n M₁ M₂
    (fun A B dir => sourceConeCircle (sourceParentAxis X Y) dir *
      sourceParentInactiveSelection N sig t X Y A B dir) b₁ b₂

noncomputable def sourceParentRetainedF (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (ρ ν : Measure Plane) (n : ℕ)
    (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) : ℝ → ℂ :=
  sourceCellwiseDistanceF X Y ρ ν n n M₁ M₂
    (fun A B dir => sourceConeCircle (sourceParentAxis X Y) dir *
      (1-sourceParentInactiveSelection N sig t X Y A B dir)) b₁ b₂

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SelectedDistanceAssembly
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def distanceBinIntegrand (ρ ν : Measure Plane) (X Y : Set Plane)
    (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) (axis : ℝ) (n j : ℕ)
    (z : ℝ × UnitCircle) : ℂ :=
  (sourceConeCircle axis z.2 * rotatedBinSelection n {j} axis z.2) *
    sourceAngularTransform ρ X M₁ b₁ z.1 z.2 *
      conj (sourceAngularTransform ν Y M₂ b₂ z.1 z.2)

noncomputable def sourceParentActiveLabels (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (A B : CellPath) : Finset ℕ :=
  Finset.range (angularBinCount (graphUncappedAngularScale N sig t)) \
    inactiveAngularLabels (angularBinCount (graphUncappedAngularScale N sig t))
      (sourceCenteredCellDirection X Y (X.descendant A) (Y.descendant B))
      (3*graphUncappedAngularScale N sig t)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ParentBinFamily
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def sourceParentBinLabels (N : ℕ) (sig t : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (n : ℕ) : Finset ParentDistanceBinLabel :=
  ((occupiedAnchorPaths X ρ n) ×ˢ (occupiedAnchorPaths Y ν n)).sigma
    (fun AB => sourceParentActiveLabels N sig t X Y AB.1 AB.2)

noncomputable def sourceParentBinIntegrand (N : ℕ) (sig t : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (e : ParentDistanceBinLabel) : ℝ × UnitCircle → ℂ :=
  distanceBinIntegrand ρ ν (X.descendant e.1.1).carrier (Y.descendant e.1.2).carrier
    M₁ M₂ b₁ b₂ (sourceParentAxis X Y) (angularBinCount (graphUncappedAngularScale N sig t)) e.2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ParentGraphEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def sourceParentGraphTerm (N : ℕ) (sig t v : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (Ψ : ℝ → ℝ) (e f : ParentDistanceBinLabel) : ℂ :=
  graphOriginalTerm ![ρ,ν,ν,ρ]
    ![(X.descendant e.1.1).carrier,(Y.descendant e.1.2).carrier,
      (Y.descendant f.1.2).carrier,(X.descendant f.1.1).carrier]
    ![M₁,M₂,M₂,M₁] ![b₁,b₂,b₂,b₁] true true (sourceParentAxis X Y)
    (graphUncappedAngularScale N sig t) v e.2 f.2 Ψ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ParentGraphIndices
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def sourceParentGraphIndex (A B : CellPath) (ef : ParentDistanceBinLabel × ParentDistanceBinLabel) :
    GraphNonedgeIndex :=
  (((A++ef.1.1.1,B++ef.1.1.2),(B++ef.2.1.2,A++ef.2.1.1)),((ef.1.2,ef.2.2),true))

noncomputable def sourceParentGraphIndices (N : ℕ) (sig t : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (n : ℕ) (A B : CellPath) : Finset GraphNonedgeIndex := by
  classical
  exact ((sourceParentBinLabels N sig t X Y ρ ν n) ×ˢ
    (sourceParentBinLabels N sig t X Y ρ ν n)).image (sourceParentGraphIndex A B)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceEligibleIndices
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def graphDistanceEligibleIndices (I : Finset GraphNonedgeIndex)
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (m : ℕ) (axis : ℝ) : Finset GraphNonedgeIndex := by
  classical
  exact I.filter (GraphDistanceIndexEligible Q₁ Q₂ ρ ν β γ m axis)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_DistancePairDegree
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def distancePairCells (Q₁ Q₂ : DyadicSquare) (row col : CellPath × CellPath) :
    Fin 4 → DyadicSquare :=
  ![Q₁.descendant row.1,Q₂.descendant col.1,Q₂.descendant row.2,Q₁.descendant col.2]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceMatrixData
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def sourceRetainedDistanceIndices
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (A B : CellPath) (a n N : ℕ) (sig t θ : ℝ)
    (rep : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle) : Finset GraphNonedgeIndex :=
  graphDistanceEligibleIndices (graphRetainedIndices
    (sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
    N sig (a+n) true ![Q₁,Q₂,Q₂,Q₁] rep)
    Q₁ Q₂ ρ ν β γ (angularBinCount θ) (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_RootPairSymbols
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def rootPairSymbol (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) (dir : UnitCircle) : ℂ :=
  (d.mask N sig z.1 dir : ℂ)*(e.mask N sig z.2 dir : ℂ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootLeibniz
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def rootAngleFactor (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) : RootMaskIndex → ℝ → ℝ :=
  Sum.elim
    (fun b => descriptorAngleMask d.Q d.ρ d.mass N d.lam sig d.J d.i b z.1)
    (fun b => descriptorAngleMask e.Q e.ρ e.mass N e.lam sig e.J e.i b z.2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootSpatialTerms
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

noncomputable def rootDistanceEndpointKernel (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (U V : DyadicSquare) (j : ℕ) (k : RootMaskIndex → ℕ) (r : ℝ) (z : Plane × Plane) : ℂ :=
  (((dist z.1 z.2)⁻¹)^j:ℝ) * sourceDistanceKernel (sourceConeCircle (sourceParentAxis U V))
    (rootLeftSymbol d N sig k) (rootRightSymbol e N sig k) r z.1 z.2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_FourSpatialPairMeasure
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

def fourSpatialPairEquiv : (Fin 4 → Plane) ≃ᵐ ((Plane × Plane) × (Plane × Plane)) where
  toFun x := ((x 0,x 1),(x 2,x 3))
  invFun z := ![z.1.1,z.1.2,z.2.1,z.2.2]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv z := by rcases z with ⟨⟨x,y⟩,⟨u,v⟩⟩; rfl
  measurable_toFun := by
    change Measurable (fun x : Fin 4 → Plane => ((x 0,x 1),(x 2,x 3)))
    fun_prop
  measurable_invFun := by
    apply Measurable.of_eval
    intro i
    change Measurable (fun z : (Plane × Plane) × (Plane × Plane) =>
      (![z.1.1,z.1.2,z.2.1,z.2.2] : Fin 4 → Plane) i)
    fin_cases i <;> fun_prop

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_GoodSupportedKernelMajorant
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def distanceDifferenceKernel (v : ℝ) (x : Fin 4 → Plane) : ℝ≥0∞ :=
  ENNReal.ofReal (1/(1+(2:ℝ)^v*|dist (x 0) (x 1)-dist (x 2) (x 3)|)^2)

def fourPairGood (G H : Set (Plane × Plane)) : Set (Fin 4 → Plane) :=
  fourSpatialPairEquiv ⁻¹' (G ×ˢ H)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_Shells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set ComplexConjugate
open scoped ENNReal

theorem dyadicShell_compact (N : ℕ) : IsCompact (dyadicShell N) := by
  have hc : IsClosed (dyadicShell N) :=
    (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  apply isCompact_Icc.of_isClosed_subset hc
  intro r hr
  exact abs_le.mp hr.2

theorem shell_energy_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (N : ℕ) :
    IntegrableOn (fun r => ‖charFun μ r‖^2) (dyadicShell N) volume := by
  exact ((continuous_charFun.norm.pow 2).continuousOn).integrableOn_compact
    (dyadicShell_compact N)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_DistanceSupportedGraph
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def graphSupportedDistanceIndices (I : Finset GraphNonedgeIndex) (θ axis : ℝ) :
    Finset GraphNonedgeIndex := by
  classical
  exact I.filter (fun e => (tsupport (graphSourceWeight true e.2.2 axis
    (angularBinCount θ) e.2.1.1 e.2.1.2)).Nonempty)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SpatialLeibnizSubpower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def spatialLeibnizCost (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (A : ℕ → ℝ) (N q a t : ℕ) : ℝ :=
  spatialFourierCost δ L hδ hL j *
    (((inverseLeibnizTerms j (pairMaskIndices (policyDescriptorList A N q a t))).map
      (fun b => ‖b.1‖)).sum * (2:ℝ)^j)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_OuterChildProfileBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

noncomputable def outerChildEnergy (Q : Fin 2 → DyadicSquare)
    (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (N q c J : ℕ)
    (lam sig : ℝ) (k : Fin 2 → PolicyDescriptor → ℕ)
    (h : Fin 2 → Plane → ℂ) (Ψ : ℝ → ℝ) (row : CellPath × CellPath) : ℝ≥0∞ :=
  sourceAngularH c N Ψ
    (fun z => sourceAngularTransform (ρ 0) ((Q 0).descendant row.1).carrier
      (((2:ℝ)^N)^(-mass 0 c))
      (inheritedCircleSymbol (outerDescriptorList (mass 0) N q c) id (k 0)
        (Q 0) (ρ 0) (mass 0) N lam sig J 0 (h 0)) z.1 z.2)
    (fun z => sourceAngularTransform (ρ 1) ((Q 1).descendant row.2).carrier
      (((2:ℝ)^N)^(-mass 1 c))
      (inheritedCircleSymbol (outerDescriptorList (mass 1) N q c) id (k 1)
        (Q 1) (ρ 1) (mass 1) N lam sig J 0 (h 1)) z.1 z.2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_SmoothShellPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceShellBand_support (n : ℕ) : Function.support (sourceShellBand n) ⊆ dyadicShell (n+1) := by
  intro r hr
  have h := sourceShellBand_support_bounds n hr
  change (2:ℝ)^((↑(n+1 : ℕ):ℝ)-1) ≤ |r| ∧ |r| ≤ (2:ℝ)^((↑(n+1 : ℕ):ℝ)+1)
  rw [show (↑(n+1 : ℕ):ℝ)-1 = (n:ℝ) by push_cast; ring,
    show (↑(n+1 : ℕ):ℝ)+1 = (↑(n+2 : ℕ):ℝ) by push_cast; ring,
    Real.rpow_natCast, Real.rpow_natCast]
  exact h

theorem sourceShellBand_compact (n : ℕ) : HasCompactSupport (sourceShellBand n) :=
  HasCompactSupport.intro (dyadicShell_compact (n+1)) (fun r hr => by
    by_contra h
    exact hr (sourceShellBand_support n h))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ShellKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped SchwartzMap FourierTransform

noncomputable def sourceShellSchwartz (n : ℕ) : 𝓢(ℝ, ℂ) :=
  ((sourceShellBand_compact n).toSchwartzMap (sourceShellBand_smooth n)).postcompCLM
    Complex.ofRealCLM

@[simp] theorem sourceShellSchwartz_apply (n : ℕ) (r : ℝ) :
    sourceShellSchwartz n r = (sourceShellBand n r : ℂ) := rfl

noncomputable def sourceShellKernel (n : ℕ) : ℝ → ℂ := sourceInverseKernel (sourceShellSchwartz n)

theorem sourceShellKernel_integrable (n : ℕ) : Integrable (sourceShellKernel n) := by
  have h := ((𝓕 (sourceShellSchwartz n)).integrable.comp_div
    (by positivity : 2*Real.pi ≠ 0)).smul ((2*Real.pi)⁻¹)
  change Integrable (fun x => (2*Real.pi)⁻¹ • 𝓕 (⇑(sourceShellSchwartz n)) (x/(2*Real.pi)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  rw [Pi.smul_apply, SchwartzMap.fourier_coe]

theorem sourceShellBand_dilate (n : ℕ) (r : ℝ) :
    sourceShellBand n r = sourceShellBand 0 (r/(2:ℝ)^n) := by
  simp only [sourceShellBand, sourceShellLowpass, zero_add, pow_zero, pow_one, div_one]
  congr 1
  rw [pow_succ, div_div]

theorem sourceShellKernel_dilate (n : ℕ) (x : ℝ) :
    sourceShellKernel n x = (2:ℝ)^n • sourceShellKernel 0 ((2:ℝ)^n*x) := by
  have he : (sourceShellSchwartz n : ℝ → ℂ) =
      fun r => sourceShellSchwartz 0 (r/(2:ℝ)^n) := by
    funext r
    simp only [sourceShellSchwartz_apply, sourceShellBand_dilate n r]
  rw [sourceShellKernel, he, sourceInverseKernel_dilate _ (by positivity),
    abs_of_pos (by positivity : (0:ℝ)<2^n)]
  rfl

theorem sourceShellKernel_uniform_L1 (n : ℕ) :
    (∫ x, ‖sourceShellKernel n x‖) = ∫ x, ‖sourceShellKernel 0 x‖ := by
  simp_rw [sourceShellKernel_dilate n, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ)<2^n)]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x => ‖sourceShellKernel 0 x‖) ((2:ℝ)^n), smul_eq_mul,
    abs_of_pos (by positivity : (0:ℝ)<(2^n)⁻¹)]
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_MeasureKernelConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform

theorem sourceShellKernel_continuous (n : ℕ) : Continuous (sourceShellKernel n) := by
  have h := (𝓕 (sourceShellSchwartz n)).continuous.comp
    (continuous_id.div_const (2*Real.pi))
  change Continuous (fun x => (2*Real.pi)⁻¹ • 𝓕 (⇑(sourceShellSchwartz n)) (x/(2*Real.pi)))
  convert (continuous_const (y := (2*Real.pi)⁻¹)).smul h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [id_eq, SchwartzMap.fourier_coe]
  rfl

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SignedConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter

 theorem shellKernelMeasureConvolution_sub_L1 (τ σ : Measure ℝ)
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] (n : ℕ) :
    Integrable (fun x => kernelMeasureConvolution (sourceShellKernel n) τ x-
      kernelMeasureConvolution (sourceShellKernel n) σ x) ∧
    (∫ x, ‖kernelMeasureConvolution (sourceShellKernel n) τ x-
      kernelMeasureConvolution (sourceShellKernel n) σ x‖) ≤
      (τ.toSignedMeasure-σ.toSignedMeasure).totalVariation.real univ *
      ∫ x, ‖sourceShellKernel 0 x‖ := by
  simpa only [sourceShellKernel_uniform_L1] using kernelMeasureConvolution_sub_L1
    (sourceShellKernel n) (sourceShellKernel_continuous n) (sourceShellKernel_integrable n) τ σ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SmoothConvolution
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal Convolution

noncomputable def sourceSmoothDensity (α : Measure Plane) (b : Plane → ℝ) (x : Plane) : ℝ :=
  ∫ y, b (x-y) ∂α

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ShellFrequencyEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem sourceShellMultiplier_zero (τ : Measure ℝ) (n : ℕ) (r : ℝ)
    (hr : r ∉ dyadicShell (n+1)) : sourceShellMultiplier τ n r = 0 := by
  have he : sourceShellBand n r = 0 := by
    by_contra hn
    exact hr (sourceShellBand_support n hn)
  simp only [sourceShellMultiplier, he, Complex.ofReal_zero, zero_mul]

theorem sourceShellMultiplier_compact (τ : Measure ℝ) (n : ℕ) :
    HasCompactSupport (sourceShellMultiplier τ n) :=
  HasCompactSupport.intro (dyadicShell_compact (n+1)) (sourceShellMultiplier_zero τ n)

theorem sourceShellMultiplier_memLp (τ : Measure ℝ) [IsFiniteMeasure τ] (n : ℕ) (p : ℝ≥0∞) :
    MemLp (sourceShellMultiplier τ n) p volume :=
  (sourceShellMultiplier_continuous τ n).memLp_of_hasCompactSupport
    (sourceShellMultiplier_compact τ n)

theorem sourceShellMultiplier_energy_le (τ : Measure ℝ) [IsFiniteMeasure τ] (n : ℕ) :
    (∫ r, ‖sourceShellMultiplier τ n r‖^2) ≤ shellEnergy τ (n+1) := by
  have he : (∫ r in dyadicShell (n+1), ‖sourceShellMultiplier τ n r‖^2) =
      ∫ r, ‖sourceShellMultiplier τ n r‖^2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr => by
      rw [sourceShellMultiplier_zero τ n r hr, norm_zero, zero_pow (by norm_num)])
  rw [← he]
  apply setIntegral_mono_on
    (((sourceShellMultiplier_continuous τ n).norm.pow 2).continuousOn.integrableOn_compact
      (dyadicShell_compact (n+1))) (shell_energy_integrable τ (n+1))
    (dyadicShell_compact (n+1)).measurableSet
  intro r _
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [sourceShellMultiplier, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (sourceShellBand_abs_le n r) (norm_nonneg _)).trans_eq
    (one_mul _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_KernelFourierIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter

theorem shellKernelMeasureConvolution_fourier (τ : Measure ℝ) [IsFiniteMeasure τ]
    (n : ℕ) (x : ℝ) :
    kernelMeasureConvolution (sourceShellKernel n) τ x =
      sourceInverseKernel (sourceShellMultiplier τ n) x := by
  exact sourceInverseKernel_measure (sourceShellSchwartz n)
    (sourceShellSchwartz n).continuous (sourceShellSchwartz n).integrable τ x

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_RootPatchGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

noncomputable def rootPatchEnvelope (x : Plane) (r : ℝ) : DyadicSquare :=
  ⟨x 0-2*r,x 1-2*r,4*r⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_SourceSpatialEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace

 theorem shellKernelMeasureConvolution_L2 (τ : Measure ℝ) [IsFiniteMeasure τ] (n : ℕ) :
    MemLp (kernelMeasureConvolution (sourceShellKernel n) τ) 2 volume ∧
    (∫ x, ‖kernelMeasureConvolution (sourceShellKernel n) τ x‖^2) ≤
      (2*Real.pi)⁻¹ * shellEnergy τ (n+1) := by
  have he : kernelMeasureConvolution (sourceShellKernel n) τ =
      sourceInverseKernel (sourceShellMultiplier τ n) := funext
    (shellKernelMeasureConvolution_fourier τ n)
  rw [he]
  have h1 : Integrable (sourceShellMultiplier τ n) :=
    memLp_one_iff_integrable.mp (sourceShellMultiplier_memLp τ n 1)
  have h2 := sourceShellMultiplier_memLp τ n 2
  refine ⟨sourceInverseKernel_memLp_two _ h1 h2, ?_⟩
  rw [sourceInverseKernel_plancherel _ h1 h2]
  exact mul_le_mul_of_nonneg_left (sourceShellMultiplier_energy_le τ n) (by positivity)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialTonelli
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

@[fun_prop] theorem continuous_sourceFrame_joint :
    Continuous (fun p : ℝ × (ℝ × ℝ) => sourceFrame p.1 p.2) := by
  have h : (fun p : ℝ × (ℝ × ℝ) => sourceFrame p.1 p.2) =
      fun p => p.2.1 • sourceNormal p.1 + p.2.2 • sourceDirection p.1 := by
    funext p
    exact sourceFrame_eq _ _ _
  rw [h]
  unfold sourceNormal
  fun_prop

@[fun_prop] theorem measurable_projectedDensity_joint (a : Plane → ℝ≥0∞)
    (ha : Measurable a) : Measurable (fun p : ℝ × ℝ => projectedDensity a p.1 p.2) := by
  have hc : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1,(p.1.2,p.2))) := by fun_prop
  have h : Measurable (fun p : (ℝ × ℝ) × ℝ => a (sourceFrame p.1.1 (p.1.2,p.2))) :=
    ha.comp (continuous_sourceFrame_joint.comp hc).measurable
  exact h.lintegral_prod_right'

@[fun_prop] theorem measurable_sourceRadialDensity_joint (a : Plane → ℝ≥0∞)
    (ha : Measurable a) : Measurable (fun p : Plane × ℝ => sourceRadialDensity a p.1 p.2) := by
  have h : Measurable (fun p : (Plane × ℝ) × ℝ =>
      ENNReal.ofReal p.2 * a (p.1.1 + p.2 • sourceDirection p.1.2)) := by fun_prop
  exact h.lintegral_prod_right'

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialTestEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable def radialEnergyMajorant (α β : Measure Plane) (D s t p : ℝ) : ℝ≥0∞ :=
  ((ENNReal.ofReal (D+1))^p * (ENNReal.ofReal ((D+1)^(t-(2-s)*p)))^(1/2 : ℝ)) *
    ((angularEnergyConstant (t/(2-p)))^((2-p)/2) *
      (rieszEnergy β t)^(1/2 : ℝ) * (2*rieszEnergy α s)^(p/2))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ShellSummability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable def shellL2Term (τN : ℕ → FiniteMeasure ℝ) (n : ℕ) : Lp (α := ℝ) ℂ 2 volume :=
  (shellKernelMeasureConvolution_L2 (τN (n+1)) n).1.toLp
    (kernelMeasureConvolution (sourceShellKernel n) (τN (n+1)))

noncomputable def shellL1Error (τ : FiniteMeasure ℝ) (τN : ℕ → FiniteMeasure ℝ)
    (n : ℕ) : Lp (α := ℝ) ℂ 1 volume :=
  (memLp_one_iff_integrable.mpr (shellKernelMeasureConvolution_sub_L1 τ (τN (n+1)) n).1).toLp
    (fun x => kernelMeasureConvolution (sourceShellKernel n) τ x-
      kernelMeasureConvolution (sourceShellKernel n) (τN (n+1)) x)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_TwoRootMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def twoRootPairMask (Q₀ Q₁ : DyadicSquare) (ρ ν : Measure Plane)
    (m₀ m₁ : ℝ → ℝ) (N : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane) : ENNReal :=
  let c := outerEntry m₀ m₁ N β
  ENNReal.ofReal (outerEndpointMask Q₀ ρ m₀ N lam sig kap c z.1 (sourceRadialUnit z.1 z.2) *
    outerEndpointMask Q₁ ν m₁ N lam sig kap c z.2 (sourceRadialUnit z.1 z.2))

@[fun_prop] theorem measurable_twoRootPairMask (Q₀ Q₁ : DyadicSquare) (ρ ν : Measure Plane)
    (m₀ m₁ : ℝ → ℝ) (N : ℕ) (lam sig kap β : ℝ) :
    Measurable (twoRootPairMask Q₀ Q₁ ρ ν m₀ m₁ N lam sig kap β) := by
  let entry := outerEntry m₀ m₁ N β
  let leftMask : Plane × UnitCircle → ℝ := fun endpoint =>
    outerEndpointMask Q₀ ρ m₀ N lam sig kap entry endpoint.1 endpoint.2
  let rightMask : Plane × UnitCircle → ℝ := fun endpoint =>
    outerEndpointMask Q₁ ν m₁ N lam sig kap entry endpoint.1 endpoint.2
  have hleft : Measurable leftMask :=
    measurable_outerEndpointMask Q₀ ρ m₀ N lam sig kap entry
  have hright : Measurable rightMask :=
    measurable_outerEndpointMask Q₁ ν m₁ N lam sig kap entry
  change Measurable (fun point : Plane × Plane => ENNReal.ofReal
    (leftMask (point.1, sourceRadialUnit point.1 point.2) *
      rightMask (point.2, sourceRadialUnit point.1 point.2)))
  exact ((hleft.comp (measurable_fst.prodMk measurable_sourceRadialUnit_joint)).mul
    (hright.comp (measurable_snd.prodMk measurable_sourceRadialUnit_joint))).ennreal_ofReal

theorem twoRootPairMask_le_one (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side)
    (ρ ν : Measure Plane) (m₀ m₁ : ℝ → ℝ) (N : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane) :
    twoRootPairMask Q₀ Q₁ ρ ν m₀ m₁ N lam sig kap β z ≤ 1 := by
  apply ENNReal.ofReal_le_one.mpr
  have h₀ := outerEndpointMask_bounds Q₀ hQ₀ ρ m₀ N lam sig kap (outerEntry m₀ m₁ N β) z.1 (sourceRadialUnit z.1 z.2)
  have h₁ := outerEndpointMask_bounds Q₁ hQ₁ ν m₁ N lam sig kap (outerEntry m₀ m₁ N β) z.2 (sourceRadialUnit z.1 z.2)
  nlinarith

noncomputable def retainedRootPairs (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (N B₀ B₁ : ℕ) (lam : ℝ) : Finset (List ℕ × List ℕ) :=
  (retainedClassLabels Q₀ μ N B₀ (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))).product
    (retainedClassLabels Q₁ ν N B₁ (ENNReal.ofReal (((2:ℝ)^N)^(-lam))))

noncomputable def twoRootRetainedMask (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ)
    (a : List ℕ × List ℕ) (z : Plane × Plane) : ENNReal :=
  (actualClassDomain Q₀ μ N B₀ a.1 ×ˢ actualClassDomain Q₁ ν N B₁ a.2).indicator
    (twoRootPairMask Q₀ Q₁ (actualClassMeasure Q₀ μ N B₀ a.1)
      (actualClassMeasure Q₁ ν N B₁ a.2) (m₀ a.1) (m₁ a.2) N lam sig kap β) z

noncomputable def restoredTwoRootMask (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane) : ENNReal :=
  ∑ a ∈ retainedRootPairs Q₀ Q₁ μ ν N B₀ B₁ lam,
    twoRootRetainedMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a z

@[fun_prop] theorem measurable_twoRootRetainedMask (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) (a : List ℕ × List ℕ) :
    Measurable (twoRootRetainedMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a) :=
  (measurable_twoRootPairMask ..).indicator
    ((measurableSet_actualClassDomain ..).prod (measurableSet_actualClassDomain ..))

@[fun_prop] theorem measurable_restoredTwoRootMask (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) :
    Measurable (restoredTwoRootMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β) :=
  Finset.measurable_sum _ (fun _ _ => measurable_twoRootRetainedMask ..)

theorem twoRoot_domain_unique (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side)
    (μ ν : Measure Plane) (N B₀ B₁ : ℕ) {a b : List ℕ × List ℕ} {z : Plane × Plane}
    (ha : z ∈ actualClassDomain Q₀ μ N B₀ a.1 ×ˢ actualClassDomain Q₁ ν N B₁ a.2)
    (hb : z ∈ actualClassDomain Q₀ μ N B₀ b.1 ×ˢ actualClassDomain Q₁ ν N B₁ b.2) : a = b := by
  apply Prod.ext
  · by_contra hn
    exact Set.disjoint_left.mp (actualClassDomain_disjoint Q₀ hQ₀ μ N B₀ hn) ha.1 hb.1
  · by_contra hn
    exact Set.disjoint_left.mp (actualClassDomain_disjoint Q₁ hQ₁ ν N B₁ hn) ha.2 hb.2

theorem restoredTwoRootMask_on_pair (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side)
    (μ ν : Measure Plane) (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ)
    {a : List ℕ × List ℕ} (ha : a ∈ retainedRootPairs Q₀ Q₁ μ ν N B₀ B₁ lam) {z : Plane × Plane}
    (hz : z ∈ actualClassDomain Q₀ μ N B₀ a.1 ×ˢ actualClassDomain Q₁ ν N B₁ a.2) :
    restoredTwoRootMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β z =
      twoRootPairMask Q₀ Q₁ (actualClassMeasure Q₀ μ N B₀ a.1)
        (actualClassMeasure Q₁ ν N B₁ a.2) (m₀ a.1) (m₁ a.2) N lam sig kap β z := by
  classical
  rw [restoredTwoRootMask, Finset.sum_eq_single a]
  · exact Set.indicator_of_mem hz _
  · intro b _ hba
    apply Set.indicator_of_notMem
    exact fun hb => hba (twoRoot_domain_unique Q₀ Q₁ hQ₀ hQ₁ μ ν N B₀ B₁ hb hz)
  · exact fun hn => (hn ha).elim

theorem restoredTwoRootMask_discarded (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) {z : Plane × Plane}
    (hz : z.1 ∉ retainedClassUnion Q₀ μ N B₀ (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) ∨
      z.2 ∉ retainedClassUnion Q₁ ν N B₁ (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))) :
    restoredTwoRootMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β z = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  have ha := Finset.mem_product.mp ha
  apply Set.indicator_of_notMem
  intro h
  rcases hz with hz | hz
  · exact hz (mem_iUnion₂.mpr ⟨a.1,ha.1,h.1⟩)
  · exact hz (mem_iUnion₂.mpr ⟨a.2,ha.2,h.2⟩)

theorem restoredTwoRootMask_le_one (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side)
    (μ ν : Measure Plane) (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane) :
    restoredTwoRootMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β z ≤ 1 := by
  classical
  by_cases hx : z.1 ∈ retainedClassUnion Q₀ μ N B₀ (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
  · by_cases hy : z.2 ∈ retainedClassUnion Q₁ ν N B₁ (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
    · obtain ⟨T,hT,hx⟩ := mem_iUnion₂.mp hx
      obtain ⟨U,hU,hy⟩ := mem_iUnion₂.mp hy
      rw [restoredTwoRootMask_on_pair Q₀ Q₁ hQ₀ hQ₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β
        (a := (T,U)) (Finset.mem_product.mpr ⟨hT,hU⟩) ⟨hx,hy⟩]
      exact twoRootPairMask_le_one Q₀ Q₁ hQ₀ hQ₁ ..
    · rw [restoredTwoRootMask_discarded Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β (Or.inr hy)]
      exact zero_le_one
  · rw [restoredTwoRootMask_discarded Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β (Or.inl hx)]
    exact zero_le_one

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_TwoRootCandidates
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def restoredTwoRootCandidate (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) : Measure ℝ :=
  ((μ.prod ν).withDensity (fun z => distanceWeight z*restoredTwoRootMask Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β z)).map
    (fun z => dist z.1 z.2)

noncomputable def restoredTwoRootRemoved (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) : Measure ℝ :=
  ((μ.prod ν).withDensity (fun z => distanceWeight z*(1-restoredTwoRootMask Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β z))).map
    (fun z => dist z.1 z.2)

theorem restoredTwoRootCandidate_decomposition (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) :
    weightedDistance (μ.prod ν) = restoredTwoRootCandidate Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β+
      restoredTwoRootRemoved Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β := by
  exact masked_pushforward_decomposition (μ.prod ν) (fun z => dist z.1 z.2) (by fun_prop)
    distanceWeight (restoredTwoRootMask Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β) (by unfold distanceWeight; fun_prop)
    (measurable_restoredTwoRootMask ..)
    (fun z => restoredTwoRootMask_le_one Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β z)

theorem restoredTwoRootCandidate_finite (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side) (μ ν : Measure Plane)
    [IsFiniteMeasure ((μ.prod ν).withDensity distanceWeight)]
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) :
    IsFiniteMeasure (restoredTwoRootCandidate Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β) ∧
      IsFiniteMeasure (restoredTwoRootRemoved Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β) :=
  finite_summands _ _ _ (restoredTwoRootCandidate_decomposition Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_TwoRootClassMixture
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable def twoRootClassCoefficient (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (N B₀ B₁ : ℕ) (a : List ℕ × List ℕ) : ℝ≥0 :=
  actualClassMass Q₀ μ N B₀ a.1 * actualClassMass Q₁ ν N B₁ a.2

noncomputable def twoRootClassMeasure (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ)
    (a : List ℕ × List ℕ) : Measure ℝ :=
  (RootShellData.ofOuter Q₀ Q₁ (actualClassMeasure Q₀ μ N B₀ a.1)
    (actualClassMeasure Q₁ ν N B₁ a.2) (m₀ a.1) (m₁ a.2)
    N lam lam sig kap (outerEntry (m₀ a.1) (m₁ a.2) N β) Q₀ Q₁).measure

end PlanarFalconer

end OAI
end


