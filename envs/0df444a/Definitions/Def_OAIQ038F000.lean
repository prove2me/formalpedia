-- Prove2me | Definitions.Def_OAIQ038F000
-- name    : OAIQ038F000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:51:41.819738+00:00
-- url     : https://prove2.me/theorems/690983d0-cc0c-4d0e-93a9-ce6bda79381e
-- title:
--   Definitions bundle OAIQ038F000 of the split of OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 453 declarations of OpenAI's Lean: 366 definitions, 19 inductive types or structures, 6 instances and 62 theorems. The definitions and types are `OAI.PlanarFalconer.ActualClassFamily`, `OAI.PlanarFalconer.AngularBinActive`, `OAI.PlanarFalconer.AngularDifferentialExpr`, `OAI.PlanarFalconer.AngularDifferentialExpr.apply`, `OAI.PlanarFalconer.AngularDifferentialExpr.cost`, `OAI.PlanarFalconer.AngularDifferentialExpr.order`, `OAI.PlanarFalconer.AngularDifferentialExpr.sum`, `OAI.PlanarFalconer.AngularDifferentialExpr.terms`, `OAI.PlanarFalconer.AngularLabelEligible`, `OAI.PlanarFalconer.AngularStateData`, `OAI.PlanarFalconer.AngularStateData.branchState`, `OAI.PlanarFalconer.AngularStateData.cellEnergy`, `OAI.PlanarFalconer.AngularStateData.childEnergy`, `OAI.PlanarFalconer.AngularStateData.childMaximum`, `OAI.PlanarFalconer.AngularStateData.children`, `OAI.PlanarFalconer.AngularStateData.contribution`, `OAI.PlanarFalconer.AngularStateData.distanceSuccessor`, `OAI.PlanarFalconer.AngularStateData.energy`, `OAI.PlanarFalconer.AngularStateData.farContribution`, `OAI.PlanarFalconer.AngularStateData.farDistanceMaximum`, `OAI.PlanarFalconer.AngularStateData.farSum`, `OAI.PlanarFalconer.AngularStateData.nearContribution`, `OAI.PlanarFalconer.AngularStateData.profile`, `OAI.PlanarFalconer.AngularStateData.retainedList`, `OAI.PlanarFalconer.AngularStateData.successor`, `OAI.PlanarFalconer.BallBound`, `OAI.PlanarFalconer.BranchLabel`, `OAI.PlanarFalconer.BranchState`, `OAI.PlanarFalconer.BranchState.Valid`, `OAI.PlanarFalconer.BranchState.angular`, `OAI.PlanarFalconer.BranchState.descriptors`, `OAI.PlanarFalconer.BranchState.finish`, `OAI.PlanarFalconer.BranchState.index`, `OAI.PlanarFalconer.BranchState.nearDepth`, `OAI.PlanarFalconer.BranchState.start`, `OAI.PlanarFalconer.BranchStep`, `OAI.PlanarFalconer.CapacityTree`, `OAI.PlanarFalconer.CapacityTree.effective`, `OAI.PlanarFalconer.CapacityTree.nonnegative`, `OAI.PlanarFalconer.CapacityTree.rootCapacity` and 345 more.
--
--   **Sources.** They come from these modules of lean/OAI/MeasureTheory/Falconer, in whole or in part: `Falconer_Angular_ActualAngleMasks`, `Falconer_Angular_ActualAngularRegularization`, `Falconer_Angular_ActualAngularTests`, `Falconer_Angular_ActualSingleStationaryKernel`, `Falconer_Angular_AngleCoordinateTests`, `Falconer_Angular_AngleMaskDerivatives`, `Falconer_Angular_AngularBinKernel`, `Falconer_Angular_AngularBinSelection`, `Falconer_Angular_AngularCellKernels`, `Falconer_Angular_AngularCellSpatialIntegral`, `Falconer_Angular_AngularDifferentialExpr`, `Falconer_Angular_AngularEnergyDropping`, `Falconer_Angular_AngularFourCellMass`, `Falconer_Angular_AngularIntegrability`, `Falconer_Angular_AngularIntegrationByParts`, `Falconer_Angular_AngularKernelIntegral`, `Falconer_Angular_AngularLabelEligibility`, `Falconer_Angular_AngularLengthPartition`, `Falconer_Angular_AngularNearNeighbors`, `Falconer_Angular_AngularNearSum`, `Falconer_Angular_AngularOperatorTerms`, `Falconer_Angular_AngularOriginalFarPartition`, `Falconer_Angular_AngularOriginalIntegrability`, `Falconer_Angular_AngularPairCircleIntegral`, `Falconer_Angular_AngularRestrictedKernel`, `Falconer_Angular_AngularStateContributions`, `Falconer_Angular_AngularStateData`, `Falconer_Angular_AngularStateSuccessor`, `Falconer_Angular_AngularStationarySpatial`, `Falconer_Angular_AngularTransportBounds`, `Falconer_Angular_AngularWidths`, `Falconer_Angular_CircleAngularBins`, `Falconer_Angular_CircleMaskCoordinates`, `Falconer_Angular_CircleMaskSupport`, `Falconer_Angular_CircleRotation`, `Falconer_Angular_FullCircleStationaryExpansion`, `Falconer_Angular_GraphRotatedWeights`, `Falconer_Angular_InheritedAngularSymbols`, `Falconer_Angular_InverseStationaryOperators`, `Falconer_Angular_LocalizedStationaryExpansion`, `Falconer_Angular_PeriodicAngularBins`, `Falconer_Angular_QuadraticStationaryExpansion`, `Falconer_Angular_RotatedConeKernel`, `Falconer_Angular_RotatedGraphEligibility`, `Falconer_Angular_SelectedAngularBins`, `Falconer_Angular_SmoothAngleMask`, `Falconer_Angular_StationaryArcLength`, `Falconer_Angular_StationaryChartAmplitude`, `Falconer_Angular_StationaryChartCutoffs`, `Falconer_Angular_StationaryDifferentialExpr`, `Falconer_Angular_StationarySineChart`, `Falconer_Estimates_ActualClassFamilies`, `Falconer_Estimates_ActualClassMass`, `Falconer_Estimates_ActualComparableFarError`, `Falconer_Estimates_ActualFarBuffer`, `Falconer_Estimates_ActualNoncomparableFar`, `Falconer_Estimates_ActualOuterMasks`, `Falconer_Estimates_ActualRegularizedClasses`, `Falconer_Estimates_ClassPruning`, `Falconer_Estimates_ComparablePositiveRebin`, `Falconer_Estimates_DistanceEligibleIndices`, `Falconer_Estimates_DistanceForm`, `Falconer_Estimates_DistanceFormFubini`, `Falconer_Estimates_DistanceMatrixData`, `Falconer_Estimates_InverseLeibniz`, `Falconer_Estimates_OccupiedPacking`, `Falconer_Estimates_OrderedLeibniz`, `Falconer_Estimates_OuterRootEquation21`, `Falconer_Estimates_PositiveDistanceGoodSet`, `Falconer_Estimates_PositiveDistanceMasks`, `Falconer_Estimates_PositiveDistanceOriginalSpatial`, `Falconer_Estimates_PositiveDistancePushforward`, `Falconer_Estimates_PositiveDistanceRebinBound`, `Falconer_Estimates_PositiveDistanceWeight`, `Falconer_Estimates_ProductMatrix`, `Falconer_Estimates_ProductOccupiedVertices`, `Falconer_Estimates_ProfileInterpolation`, `Falconer_Estimates_RegularizationLabels`, `Falconer_Estimates_RootLeibniz`, `Falconer_Estimates_RootSupremum`, `Falconer_Estimates_RootWeightedDistance`, `Falconer_Estimates_SliceAverage`, `Falconer_Estimates_SourceAssemblyParameters`, `Falconer_Estimates_SpatialAnchorMasks`, `Falconer_Estimates_WeightedDistancePushforward`, `Falconer_Fourier_BinKernel`, `Falconer_Fourier_FiberSchwartz`, `Falconer_Fourier_FourierLebesgue`, `Falconer_Fourier_FourierSlice`, `Falconer_Fourier_GraphFourPointKernel`, `Falconer_Fourier_GraphFourSymbolDerivatives`, `Falconer_Fourier_MinimalPairSymbol`, `Falconer_Fourier_NormalizedSymbolFactors`, `Falconer_Fourier_RootFourierError`, `Falconer_Fourier_RootNormalizedKernel`, `Falconer_Fourier_RootPairSymbols`, `Falconer_Fourier_SpatialAnnulusKernel`, `Falconer_Fourier_SpatialFourierIntegration`, `Falconer_Fourier_SpatialFourierSeparation`, `Falconer_Fourier_SpatialPhasedSymbols`, `Falconer_Frostman_Capacity`, `Falconer_Geometry_BinBands`, `Falconer_Geometry_BinOffsets`, `Falconer_Geometry_Bins`, `Falconer_Geometry_DyadicClasses`, `Falconer_Geometry_DyadicGeometry`, `Falconer_Geometry_DyadicPacking`, `Falconer_Geometry_InactiveBinGeometry`, `Falconer_Geometry_InactiveBinScales`, `Falconer_Geometry_ProfileGrid`, `Falconer_Geometry_RootSimilarityGeometry`, `Falconer_Geometry_ScaledDyadicPacking`, `Falconer_Geometry_SeparatedDistanceMaximum`, `Falconer_Graphs_ActualDistanceDegrees`, `Falconer_Graphs_ActualProductDegrees`, `Falconer_Graphs_EligibleProductGraphSum`, `Falconer_Graphs_Energy`, `Falconer_Graphs_GraphActualNonedgeGeometry`, `Falconer_Graphs_GraphActualQuadCells`, `Falconer_Graphs_GraphAmplitudeRepresentative`, `Falconer_Graphs_GraphChartVariation`, `Falconer_Graphs_GraphCompleteWeightSupport`, `Falconer_Graphs_GraphConeCutoff`, `Falconer_Graphs_GraphCoordinateInverse`, `Falconer_Graphs_GraphDerivativeBounds`, `Falconer_Graphs_GraphEndpointContinuity`, `Falconer_Graphs_GraphGeometry`, `Falconer_Graphs_GraphLiftJacobian`, `Falconer_Graphs_GraphNonedgeIndexCount`, `Falconer_Graphs_GraphNonedgeIntegralErrors`, `Falconer_Graphs_GraphRetainedEdges`, `Falconer_Graphs_GraphSignPartition`, `Falconer_Graphs_ParentRetainedEnergy`, `Falconer_Graphs_PrefixGraphSpecialization`, `Falconer_Graphs_PrefixSuccessorEnergy`, `Falconer_Graphs_ProductEnergyMaximum`, `Falconer_Graphs_RecursiveEnergyFamily`, `Falconer_Graphs_RootParentEnergy`, `Falconer_Measures_DyadicMeasure`, `Falconer_Measures_RootNormalizedCoefficients`, `Falconer_Radial_ProjectionDensity`, `Falconer_Radial_ProjectionEnergy`, `Falconer_Radial_RadialContinuity`, `Falconer_Radial_RadialDensity`, `Falconer_Radial_RadialFailureMass`, `Falconer_Radial_RadialShellMeasure`, `Falconer_Radial_RadialTestNorm`, `Falconer_Recursion_BlockLeafCounts`, `Falconer_Recursion_BlockRegularization`, `Falconer_Recursion_BranchAnalyticSuccessors`, `Falconer_Recursion_BranchCounts`, `Falconer_Recursion_BranchExponentAlgebra`, `Falconer_Recursion_BranchPotential`, `Falconer_Recursion_BranchTransitions`, `Falconer_Recursion_DescriptorMasks`, `Falconer_Recursion_DirectPolicyWitness`, `Falconer_Recursion_InheritedPolicyState`, `Falconer_Recursion_InteriorPolicy`, `Falconer_Recursion_LeafMassBins`, `Falconer_Recursion_Ledger`, `Falconer_Recursion_ParentBinFamily`, `Falconer_Recursion_ParentConeGeometry`, `Falconer_Recursion_ParentHFBridge`, `Falconer_Recursion_PolicyDescriptors`, `Falconer_Recursion_Potential`, `Falconer_Recursion_PrefixLowMaximum`, `Falconer_Recursion_ReachedBranchWeights`, `Falconer_Recursion_ReachedStateRecursion`, `Falconer_Recursion_RecursiveCellInvariants`, `Falconer_Recursion_RetainedPairMasks`, `Falconer_Recursion_SourceBranchDepth`, `Falconer_Recursion_SuffixRetainedPairs`, `Falconer_Recursion_TwoProfileRecursion`, `Falconer_Shells_AngularShellEnergy`, `Falconer_Shells_HighShellEndpointTerms`, `Falconer_Shells_HighShellFourierError`, `Falconer_Shells_HighShellLeibnizSymbols`, `Falconer_Shells_HighShellMixture`, `Falconer_Shells_HighShellOrderForm`, `Falconer_Shells_HighShellParentEnergy`, `Falconer_Shells_HighShellSeparatedTerms`, `Falconer_Shells_HighShellSupremum`, `Falconer_Shells_NormalizedHighShellKernel`, `Falconer_Shells_RootEndpointData`, `Falconer_Shells_RootEndpointTerms`, `Falconer_Shells_RootShellData`, `Falconer_Shells_RootShellMixture`, `Falconer_Shells_RootShellOrder`, `Falconer_Shells_Shells`.
--
--   **Imports.** It imports the published bundle `Def_PlanarFalconer`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ038F002`; the statements `OAI.PlanarFalconer.PositiveDistanceData.inverseOrderForm_shell`, `OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF_measurable`, `OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_parent_bound`, `OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_profile_error`, `OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_band`, `OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_graph`, `OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_high_shell`, `OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_inverse_supremum`, `OAI.PlanarFalconer.RootShellData.inverseOrderForm_shell`, `OAI.PlanarFalconer.RootShellData.mainF_shell`, `OAI.PlanarFalconer.RootShellData.uniform_parent_bound`, `OAI.PlanarFalconer.actual_angular_near_fixed`, `OAI.PlanarFalconer.actual_profile_regularization`, `OAI.PlanarFalconer.full_circle_stationary_expansion`, `OAI.PlanarFalconer.source_angular_direct`, `OAI.PlanarFalconer.source_positive_distance_suffix`, `OAI.PlanarFalconer.stationary_product_radial_bound`, `OAI.PlanarFalconer.uniform_actual_angular_recursion_bound`, `OAI.PlanarFalconer.uniform_actual_comparable_far_error`, `OAI.PlanarFalconer.uniform_actual_distance_equation12`, `OAI.PlanarFalconer.uniform_actual_distance_low_band`, `OAI.PlanarFalconer.uniform_actual_far_radial_error`, `OAI.PlanarFalconer.uniform_actual_far_source_equation24`, `OAI.PlanarFalconer.uniform_actual_far_stationary_integrable`, `OAI.PlanarFalconer.uniform_actual_far_stationary_reduction`, `OAI.PlanarFalconer.uniform_actual_four_approximant_good`, `OAI.PlanarFalconer.uniform_actual_noncomparable_radial_either`, `OAI.PlanarFalconer.uniform_actual_product_estimate`, `OAI.PlanarFalconer.uniform_actual_recursive_profile`, `OAI.PlanarFalconer.uniform_actual_single_stationary_kernel`, `OAI.PlanarFalconer.uniform_actual_suffix_local_bins`, `OAI.PlanarFalconer.uniform_independent_class_equation27`, `OAI.PlanarFalconer.uniform_outer_root_graph_bound`, `OAI.PlanarFalconer.uniform_recursive_energy_rules` and `OAI.PlanarFalconer.uniform_root_fourier_error`; the proof of `OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_graph`.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/MeasureTheory/Falconer at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer

section
-- module Solutions.OAIQ038_FA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

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

noncomputable def angleBump (η : ℝ) (hη : 0 < η) : ContDiffBump (0:ℝ) :=
  ⟨η/2,η,half_pos hη,half_lt_self hη⟩

noncomputable def thickenedIndicator (G : Set ℝ) (η : ℝ) : ℝ → ℝ :=
  (thickening (2*η) G).indicator (fun _ => 1)

noncomputable def smoothAngleMask (G : Set ℝ) (η : ℝ) (hη : 0 < η) : ℝ → ℝ :=
  (angleBump η hη).normed volume ⋆[lsmul ℝ ℝ,volume] thickenedIndicator G η

theorem thickenedIndicator_locallyIntegrable (G : Set ℝ) (η : ℝ) :
    LocallyIntegrable (thickenedIndicator G η) volume :=
  (continuous_const.locallyIntegrable (μ := volume)).indicator isOpen_thickening.measurableSet

theorem smoothAngleMask_contDiff (G : Set ℝ) (η : ℝ) (hη : 0 < η) :
    ContDiff ℝ ∞ (smoothAngleMask G η hη) :=
  (angleBump η hη).hasCompactSupport_normed.contDiff_convolution_left _
    (angleBump η hη).contDiff_normed (thickenedIndicator_locallyIntegrable G η)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Frostman_Capacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

inductive CapacityTree where
  | leaf (cap : ℝ)
  | node (cap : ℝ) (t₀ t₁ t₂ t₃ : CapacityTree)

def CapacityTree.rootCapacity : CapacityTree → ℝ
  | .leaf c => c
  | .node c _ _ _ _ => c

def CapacityTree.nonnegative : CapacityTree → Prop
  | .leaf c => 0 ≤ c
  | .node c t₀ t₁ t₂ t₃ =>
      0 ≤ c ∧ t₀.nonnegative ∧ t₁.nonnegative ∧ t₂.nonnegative ∧ t₃.nonnegative

noncomputable def CapacityTree.effective : CapacityTree → ℝ
  | .leaf c => c
  | .node c t₀ t₁ t₂ t₃ => min c (t₀.effective+t₁.effective+t₂.effective+t₃.effective)

inductive Routes : CapacityTree → ℝ → Prop where
  | leaf {c m} (hm : 0 ≤ m) (hc : m ≤ c) : Routes (.leaf c) m
  | node {c t₀ t₁ t₂ t₃ m m₀ m₁ m₂ m₃}
      (hm : 0 ≤ m) (hc : m ≤ c) (hsum : m₀+m₁+m₂+m₃=m)
      (h₀ : Routes t₀ m₀) (h₁ : Routes t₁ m₁)
      (h₂ : Routes t₂ m₂) (h₃ : Routes t₃ m₃) :
      Routes (.node c t₀ t₁ t₂ t₃) m

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

structure DyadicSquare where
  x : ℝ
  y : ℝ
  side : ℝ

def DyadicSquare.carrier (Q : DyadicSquare) : Set Plane :=
  {z | Q.x ≤ z 0 ∧ z 0 < Q.x + Q.side ∧
       Q.y ≤ z 1 ∧ z 1 < Q.y + Q.side}

noncomputable def DyadicSquare.child (Q : DyadicSquare) (i j : Bool) : DyadicSquare :=
  ⟨Q.x + (if i then Q.side / 2 else 0),
   Q.y + (if j then Q.side / 2 else 0), Q.side / 2⟩

theorem DyadicSquare.child_side_pos (Q : DyadicSquare) (hQ : 0 < Q.side)
    (i j : Bool) : 0 < (Q.child i j).side := by
  dsimp [child]
  positivity

theorem DyadicSquare.measurable (Q : DyadicSquare) : MeasurableSet Q.carrier := by
  have h0 : Continuous (fun z : Plane => z 0) := (EuclideanSpace.proj 0).continuous
  have h1 : Continuous (fun z : Plane => z 1) := (EuclideanSpace.proj 1).continuous
  exact (isClosed_le continuous_const h0).measurableSet.inter
    ((isOpen_lt h0 continuous_const).measurableSet.inter
    ((isClosed_le continuous_const h1).measurableSet.inter
    (isOpen_lt h1 continuous_const).measurableSet))

theorem DyadicSquare.child_subset (Q : DyadicSquare) (hQ : 0 ≤ Q.side)
    (i j : Bool) : (Q.child i j).carrier ⊆ Q.carrier := by
  have halfSide_nonneg : 0 ≤ Q.side / 2 := div_nonneg hQ (by norm_num)
  intro z hz
  cases i <;> cases j <;>
    simp only [carrier, child, Bool.false_eq_true, ↓reduceIte,
      add_zero, mem_ofPred_eq] at * <;>
    refine ⟨by linarith [halfSide_nonneg], by linarith [halfSide_nonneg],
      by linarith [halfSide_nonneg], by linarith [halfSide_nonneg]⟩

theorem DyadicSquare.children_disjoint (Q : DyadicSquare)
    {i j i' j' : Bool} (h : (i,j) ≠ (i',j')) :
    Disjoint (Q.child i j).carrier (Q.child i' j').carrier := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  cases i <;> cases j <;> cases i' <;> cases j' <;>
    simp_all only [carrier, child, Bool.false_eq_true, ↓reduceIte,
      add_zero, mem_ofPred_eq, ne_eq, not_true_eq_false] <;> linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_DyadicMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable def DyadicSquare.descendant (Q : DyadicSquare) :
    List (Bool × Bool) → DyadicSquare
  | [] => Q
  | (i,j) :: p => (Q.child i j).descendant p

theorem DyadicSquare.descendant_subset (Q : DyadicSquare) (hQ : 0 < Q.side)
    (p : List (Bool × Bool)) : (Q.descendant p).carrier ⊆ Q.carrier := by
  induction p generalizing Q with
  | nil => exact Subset.rfl
  | cons a p ih =>
    exact (ih _ (Q.child_side_pos hQ a.1 a.2)).trans (Q.child_subset hQ.le a.1 a.2)

def DyadicMassBounds (s : ℝ) (Q : DyadicSquare) (K : ℕ) (μ : Measure Plane) : Prop :=
  ∀ p : List (Bool × Bool), p.length ≤ K →
    μ (Q.descendant p).carrier ≤ ENNReal.ofReal ((Q.descendant p).side ^ s)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

def dyadicPaths : ℕ → Finset (List (Bool × Bool))
  | 0 => {[]}
  | n+1 => Finset.univ.biUnion fun a : Bool × Bool =>
      (dyadicPaths n).image (List.cons a)

@[simp] theorem mem_dyadicPaths (n : ℕ) (p : List (Bool × Bool)) :
    p ∈ dyadicPaths n ↔ p.length = n := by
  induction n generalizing p with
  | zero => simp [dyadicPaths]
  | succ n ih =>
    cases p with
    | nil => simp [dyadicPaths]
    | cons a p => simp [dyadicPaths, ih]

theorem DyadicSquare.descendants_disjoint (Q : DyadicSquare) (hQ : 0 < Q.side)
    {p q : List (Bool × Bool)} (hlen : p.length = q.length) (hne : p ≠ q) :
    Disjoint (Q.descendant p).carrier (Q.descendant q).carrier := by
  induction p generalizing Q q with
  | nil =>
    have : q = [] := by cases q <;> simp_all
    exact (hne this.symm).elim
  | cons a p ih =>
    cases q with
    | nil => simp at hlen
    | cons b q =>
      by_cases hab : a = b
      · subst b
        exact ih _ (Q.child_side_pos hQ a.1 a.2) (by simpa using hlen)
          (by intro he; exact hne (he ▸ rfl))
      · exact (Q.children_disjoint hab).mono
          ((Q.child a.1 a.2).descendant_subset (Q.child_side_pos hQ a.1 a.2) p)
          ((Q.child b.1 b.2).descendant_subset (Q.child_side_pos hQ b.1 b.2) q)

def DyadicSquare.box (Q : DyadicSquare) : Set (ℝ × ℝ) :=
  Ico Q.x (Q.x+Q.side) ×ˢ Ico Q.y (Q.y+Q.side)

def pairToPlane (z : ℝ × ℝ) : Plane := WithLp.toLp 2 ![z.1,z.2]

@[simp] theorem pairToPlane_mem (Q : DyadicSquare) (z : ℝ × ℝ) :
    pairToPlane z ∈ Q.carrier ↔ z ∈ Q.box := by
  simp only [pairToPlane, DyadicSquare.carrier, DyadicSquare.box,
    mem_ofPred_eq, mem_prod, mem_Ico,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_ScaledDyadicPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def DyadicSquare.center (Q : DyadicSquare) : Plane :=
  WithLp.toLp 2 ![Q.x+Q.side/2,Q.y+Q.side/2]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RegularizationLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

abbrev CellPath := List (Bool × Bool)

noncomputable def labeledChildren (L : Finset CellPath) (f : CellPath → List ℕ)
    (a b : ℕ) (p : CellPath) : Finset CellPath := by
  classical
  exact (L.filter fun q => q.take a = p.take a ∧ f q = f p).image (List.take b)

noncomputable def extendLabel (L : Finset CellPath) (a b : ℕ)
    (f : CellPath → List ℕ) (p : CellPath) : List ℕ :=
  Nat.log 2 (labeledChildren L f a b p).card :: f p

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def leafUnion (Q : DyadicSquare) (L : Finset (List (Bool × Bool))) : Set Plane :=
  ⋃ p ∈ L, (Q.descendant p).carrier

theorem leafUnion_disjoint (Q : DyadicSquare) (hQ : 0 < Q.side) {N : ℕ}
    {L T : Finset (List (Bool × Bool))} (hL : L ⊆ dyadicPaths N)
    (hT : T ⊆ dyadicPaths N) (h : Disjoint L T) :
    Disjoint (leafUnion Q L) (leafUnion Q T) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨p,hp,hzp⟩ := mem_iUnion₂.mp hz
  obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz'
  have hne : p ≠ q := by
    intro he; subst q; exact Finset.disjoint_left.mp h hp hq
  exact Set.disjoint_left.mp (Q.descendants_disjoint hQ
    ((mem_dyadicPaths _ _).mp (hL hp) |>.trans ((mem_dyadicPaths _ _).mp (hT hq)).symm)
    hne) hzp hzq

noncomputable def retainedLeaves (Q : DyadicSquare) (μ : Measure Plane) (N : ℕ)
    (t : ℝ≥0∞) : Finset (List (Bool × Bool)) := by
  classical
  exact (dyadicPaths N).filter fun p => t ≤ μ (Q.descendant p).carrier

noncomputable def classLeaves (L : Finset (List (Bool × Bool)))
    (f : List (Bool × Bool) → List ℕ) (T : List ℕ) : Finset (List (Bool × Bool)) := by
  classical
  exact L.filter fun p => f p = T

noncomputable def classMeasure (Q : DyadicSquare) (μ : Measure Plane)
    (L : Finset (List (Bool × Bool))) (f : List (Bool × Bool) → List ℕ) (T : List ℕ) :
    Measure Plane := μ.restrict (leafUnion Q (classLeaves L f T))

theorem classLeaves_disjoint (L : Finset (List (Bool × Bool)))
    (f : List (Bool × Bool) → List ℕ) {T U : List ℕ} (h : T ≠ U) :
    Disjoint (classLeaves L f T) (classLeaves L f U) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact h ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)

noncomputable def normalizedClass (Q : DyadicSquare) (μ : Measure Plane)
    (L : Finset (List (Bool × Bool))) (f : List (Bool × Bool) → List ℕ) (T : List ℕ) :
    Measure Plane := (classMeasure Q μ L f T univ)⁻¹ • classMeasure Q μ L f T

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_OccupiedPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def occupiedCenterCells (Q : DyadicSquare) (ν : Measure Plane)
    (p : ℕ) (x : Plane) (r : ℝ) : Finset CellPath := by
  classical
  exact (dyadicPaths p).filter fun q => 0 < ν (Q.descendant q).carrier ∧
    (Q.descendant q).center ∈ ball x r

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_LeafMassBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal

noncomputable def massBinCandidates (N : ℕ) (w : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (4*N+1)).filter fun k => (2:ℝ)^k ≤ (2:ℝ)^(4*N)*w

noncomputable def leafMassBin (N : ℕ) (w : ℝ) : ℕ :=
  if h : (massBinCandidates N w).Nonempty then (massBinCandidates N w).max' h else 0

noncomputable def sourceLeafLabel (Q : DyadicSquare) (μ : Measure Plane) (N : ℕ)
    (p : List (Bool × Bool)) : List ℕ := [leafMassBin N (μ (Q.descendant p).carrier).toReal]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BlockRegularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

abbrev blockDepth (N B i : ℕ) : ℕ := N-i*B

noncomputable def blockLabel (L : Finset CellPath) (N B : ℕ)
    (f : CellPath → List ℕ) : ℕ → CellPath → List ℕ
  | 0 => f
  | i+1 => extendLabel L (blockDepth N B (i+1)) (blockDepth N B i) (blockLabel L N B f i)

noncomputable def regularizationLeaves (Q : DyadicSquare) (μ : MeasureTheory.Measure Plane)
    (N : ℕ) : Finset CellPath := retainedLeaves Q μ N ((2:ENNReal)^(4*N))⁻¹

noncomputable def regularizationLabel (Q : DyadicSquare) (μ : MeasureTheory.Measure Plane)
    (N B : ℕ) : CellPath → List ℕ :=
  blockLabel (regularizationLeaves Q μ N) N B (sourceLeafLabel Q μ N) (N/B+1)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BlockLeafCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def blockBin (L : Finset CellPath) (F : CellPath → List ℕ)
    (N B i : ℕ) (p : CellPath) : ℕ :=
  2 ^ Nat.log 2 (labeledChildren L F (blockDepth N B (i+1)) (blockDepth N B i) p).card

noncomputable def blockProduct (L : Finset CellPath) (F : CellPath → List ℕ)
    (N B i : ℕ) (p : CellPath) : ℕ := ∏ j ∈ Finset.range i, blockBin L F N B j p

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProfileInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def blockSlope (L : Finset CellPath) (F : CellPath → List ℕ)
    (N B i : ℕ) (p : CellPath) : ℝ :=
  (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1)) (blockDepth N B i) p).card : ℝ) /
    (N:ℝ) / ((blockDepth N B i : ℝ)-(blockDepth N B (i+1) : ℝ))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_ProfileGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def blockLogProduct (L : Finset CellPath) (F : CellPath → List ℕ)
    (N B i : ℕ) (p : CellPath) : ℕ :=
  ∑ j ∈ Finset.range i,
    Nat.log 2 (labeledChildren L F (blockDepth N B (j+1)) (blockDepth N B j) p).card

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

def quarterTurn (v : Plane) : Plane := WithLp.toLp 2 ![-v 1,v 0]
def planeDot (v w : Plane) : ℝ := v 0*w 0 + v 1*w 1
noncomputable def graphA (z : ℝ) (v : Plane) : Plane := (1/2 : ℝ) • (v-z • quarterTurn v)
noncomputable def graphB (z : ℝ) (v : Plane) : Plane := (1/2 : ℝ) • (v+z • quarterTurn v)
noncomputable def graphDerivative (s : ℝ) (v w : Plane) : Plane :=
  (1/2 : ℝ) • (-quarterTurn v + s • quarterTurn w)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

def BallBound (μ : Measure Plane) (s C : ℝ) : Prop :=
  ∀ x : Plane, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology

abbrev UnitCircle := {z : Plane // ‖z‖ = 1}

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngularTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

noncomputable def stripCount {ι : Type*} (S : Finset ι) (v : ι → Plane)
    (W : ℝ) (ω : Plane) : ℕ := by
  classical
  exact (S.filter fun i => |planeDot (v i) ω| ≤ W).card

noncomputable def parallelTestCells (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) : Finset CellPath := by
  classical
  exact (dyadicPaths p).filter fun c => 0 < ρ (Q.descendant c).carrier ∧
    (Q.descendant c).center ∈ ball (Q.descendant P).center (10/(2:ℝ)^g)

noncomputable def projectionTestCells (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) : Finset CellPath := by
  classical
  exact (dyadicPaths u).filter fun c => 0 < ρ (Q.descendant c).carrier ∧ c.take p = P

noncomputable def parallelTestCount (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) (W : ℝ) (ω : Plane) : ℕ :=
  stripCount (parallelTestCells Q ρ g p P)
    (fun c => (Q.descendant c).center-(Q.descendant P).center) W (quarterTurn ω)

noncomputable def projectionTestCount (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) (W : ℝ) (ω : Plane) : ℕ :=
  let S := projectionTestCells Q ρ p u P
  stripCount (S.product S) (fun cc => (Q.descendant cc.1).center-(Q.descendant cc.2).center) W ω

noncomputable def parallelGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) (W threshold : ℝ) : Set UnitCircle :=
  {ω | (parallelTestCount Q ρ g p P W (ω:Plane):ℝ) ≤ threshold}

noncomputable def projectionGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) (W threshold : ℝ) : Set UnitCircle :=
  {ω | (projectionTestCount Q ρ p u P W (ω:Plane):ℝ) ≤ threshold}

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_FourierLebesgue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory ComplexConjugate
open scoped ENNReal NNReal RealInnerProductSpace FourierTransform

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def sourceFourier (μ : Measure V) (ξ : V) : ℂ :=
  charFun μ ((-(2 * Real.pi)) • ξ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def sineKernel (v θ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (|Real.sin θ|))^(-v)

noncomputable def angularEnergyConstant (v : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), sineKernel v θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_ProjectionEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable def sourceProjection (θ : ℝ) (z : Plane) : ℝ :=
  -Real.sin θ * z 0 + Real.cos θ * z 1

@[fun_prop] theorem continuous_sourceProjection :
    Continuous (fun p : ℝ × Plane => sourceProjection p.1 p.2) := by
  unfold sourceProjection
  fun_prop

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_FourierSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable def sourceNormal (θ : ℝ) : Plane :=
  WithLp.toLp 2 ![-Real.sin θ, Real.cos θ]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SliceAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable def sourceDirection (θ : ℝ) : Plane :=
  Complex.orthonormalBasisOneI.repr (Real.cos θ + Real.sin θ * Complex.I)

@[fun_prop] theorem continuous_sourceDirection : Continuous sourceDirection := by
  unfold sourceDirection
  fun_prop

theorem norm_sourceDirection (θ : ℝ) : ‖sourceDirection θ‖ = 1 := by
  have h := Complex.norm_polarCoord_symm (1,θ)
  rw [sourceDirection,LinearIsometryEquiv.norm_map]
  simpa only [Complex.polarCoord_symm_apply,Prod.fst,Prod.snd,Complex.ofReal_one,one_mul,abs_one] using h

noncomputable def sourceSliceEnergy (μ : Measure Plane) (s θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ r : ℝ, ENNReal.ofReal (‖sourceFourier μ (r • sourceNormal θ)‖^2) *
    ENNReal.ofReal (|r|^(s-1))

@[fun_prop] theorem measurable_sourceSliceEnergy (μ : Measure Plane) [IsFiniteMeasure μ]
    (s : ℝ) : Measurable (sourceSliceEnergy μ s) := by
  unfold sourceSliceEnergy
  have h : Measurable (fun p : ℝ × ℝ =>
    ENNReal.ofReal (‖sourceFourier μ (p.2 • sourceNormal p.1)‖^2) *
      ENNReal.ofReal (|p.2|^(s-1))) := by
    unfold sourceFourier sourceNormal
    fun_prop
  exact h.lintegral_prod_right

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_ProjectionDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable def sourceFrame (θ : ℝ) (p : ℝ × ℝ) : Plane :=
  Complex.orthonormalBasisOneI.repr
    (rotation (Circle.exp θ) (Complex.measurableEquivRealProd.symm p.swap))

theorem sourceFrame_eq (θ z r : ℝ) :
    sourceFrame θ (z,r) = z • sourceNormal θ + r • sourceDirection θ := by
  ext i
  fin_cases i <;>
    simp [sourceFrame,sourceNormal,sourceDirection,rotation_apply,Circle.coe_exp,
      Complex.exp_mul_I,Complex.measurableEquivRealProd_symm_apply,
      Complex.orthonormalBasisOneI_repr_apply, -Complex.ofReal_cos,-Complex.ofReal_sin] <;>
    simp only [← Complex.ofReal_cos,← Complex.ofReal_sin,Complex.ofReal_re] <;> ring

@[fun_prop] theorem continuous_sourceFrame (θ : ℝ) : Continuous (sourceFrame θ) := by
  have he : sourceFrame θ = fun p : ℝ × ℝ => p.1 • sourceNormal θ + p.2 • sourceDirection θ := by
    funext p
    exact sourceFrame_eq θ p.1 p.2
  rw [he]
  fun_prop

theorem sourceProjection_frame (θ z r : ℝ) : sourceProjection θ (sourceFrame θ (z,r)) = z := by
  rw [sourceFrame_eq]
  simp only [sourceProjection,sourceNormal,sourceDirection,PiLp.add_apply,PiLp.smul_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Complex.orthonormalBasisOneI_repr_apply,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,add_zero,zero_add,sub_zero,smul_eq_mul]
  nlinarith [congrArg (fun x : ℝ => z*x) (Real.sin_sq_add_cos_sq θ)]

noncomputable def projectedDensity (a : Plane → ℝ≥0∞) (θ z : ℝ) : ℝ≥0∞ :=
  ∫⁻ r : ℝ, a (sourceFrame θ (z,r))

@[fun_prop] theorem measurable_projectedDensity (a : Plane → ℝ≥0∞) (ha : Measurable a) (θ : ℝ) :
    Measurable (projectedDensity a θ) := by
  exact (ha.comp (continuous_sourceFrame θ).measurable).lintegral_prod_right'

noncomputable def sourceAlong (θ : ℝ) (x : Plane) : ℝ :=
  Real.cos θ * x 0 + Real.sin θ * x 1

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_FiberSchwartz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal SchwartzMap FourierTransform Convolution

@[fun_prop] theorem contDiff_sourceFrame (θ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (sourceFrame θ) := by
  have h : sourceFrame θ = fun p : ℝ × ℝ =>
      p.1 • sourceNormal θ + p.2 • sourceDirection θ := by
    funext p
    exact sourceFrame_eq θ p.1 p.2
  rw [h]
  fun_prop

@[fun_prop] theorem continuous_sourceAlong (θ : ℝ) : Continuous (sourceAlong θ) := by
  unfold sourceAlong
  fun_prop

theorem sourceAlong_frame (θ z r : ℝ) : sourceAlong θ (sourceFrame θ (z,r)) = r := by
  rw [sourceFrame_eq]
  simp [sourceAlong,sourceNormal,sourceDirection,
    Complex.orthonormalBasisOneI_repr_apply,-Complex.ofReal_cos,-Complex.ofReal_sin]
  nlinarith [congrArg (fun a : ℝ => r*a) (Real.sin_sq_add_cos_sq θ)]

noncomputable def sourceRealFiber (a : Plane → ℝ) (θ z : ℝ) : ℝ :=
  ∫ r : ℝ, a (sourceFrame θ (z,r))

theorem sourceRealFiber_compact (a : Plane → ℝ) (hc : HasCompactSupport a) (θ : ℝ) :
    HasCompactSupport (sourceRealFiber a θ) := by
  have hP : Continuous (sourceProjection θ) := by unfold sourceProjection; fun_prop
  apply HasCompactSupport.intro (hc.image hP)
  intro z hz
  apply integral_eq_zero_of_ae
  filter_upwards with r
  by_contra hn
  exact hz ⟨sourceFrame θ (z,r), subset_tsupport a hn, sourceProjection_frame θ z r⟩

theorem sourceRealFiber_smooth (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (θ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (sourceRealFiber a θ) := by
  let g : ℝ → ℝ → ℝ := fun z r => a (sourceFrame θ (z,r))
  have hgs : ∀ z r, z ∈ (univ : Set ℝ) → r ∉ sourceAlong θ '' tsupport a → g z r = 0 := by
    intro z r _ hr
    by_contra hn
    exact hr ⟨sourceFrame θ (z,r), subset_tsupport a hn, sourceAlong_frame θ z r⟩
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry g) (univ ×ˢ univ) :=
    (ha.comp (contDiff_sourceFrame θ)).contDiffOn
  have h := contDiffOn_convolution_right_with_param_comp (μ := (volume : Measure ℝ))
    (ContinuousLinearMap.mul ℝ ℝ) (v := fun _ : ℝ => (0 : ℝ)) contDiffOn_const
    isOpen_univ (hc.image (continuous_sourceAlong θ)) hgs
    (f := fun _ : ℝ => (1 : ℝ)) (continuous_const.locallyIntegrable) hg
  rw [contDiffOn_univ] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [convolution,ContinuousLinearMap.mul_apply',one_mul,zero_sub,g,sourceRealFiber]
  exact (integral_neg_eq_self (fun r : ℝ => a (sourceFrame θ (z,r))) volume).symm

noncomputable def sourceSchwartzFiber (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (θ : ℝ) : 𝓢(ℝ, ℝ) :=
  (sourceRealFiber_compact a hc θ).toSchwartzMap (sourceRealFiber_smooth a hc ha θ)

@[simp] theorem sourceSchwartzFiber_apply (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (θ z : ℝ) :
    sourceSchwartzFiber a hc ha θ z = ∫ r : ℝ, a (sourceFrame θ (z,r)) := rfl

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable def sourceUnitDirection (θ : ℝ) : UnitCircle :=
  ⟨sourceDirection θ,norm_sourceDirection θ⟩

@[fun_prop] theorem continuous_sourceUnitDirection : Continuous sourceUnitDirection :=
  continuous_sourceDirection.subtype_mk _

noncomputable def sourceRadialVector (x y : Plane) : Plane :=
  if y=x then sourceDirection 0 else ‖y-x‖⁻¹ • (y-x)

theorem norm_sourceRadialVector (x y : Plane) : ‖sourceRadialVector x y‖ = 1 := by
  unfold sourceRadialVector
  split_ifs with h
  · exact norm_sourceDirection _
  · exact norm_smul_inv_norm (sub_ne_zero.mpr h)

noncomputable def sourceRadialUnit (x y : Plane) : UnitCircle :=
  ⟨sourceRadialVector x y,norm_sourceRadialVector x y⟩

@[fun_prop] theorem measurable_sourceRadialUnit (x : Plane) : Measurable (sourceRadialUnit x) := by
  apply Measurable.subtype_mk
  unfold sourceRadialVector
  exact Measurable.ite (measurableSet_singleton x) measurable_const (by fun_prop)

noncomputable def sourceRadialDensity (a : Plane → ℝ≥0∞) (x : Plane) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal r * a (x+r • sourceDirection θ)

@[fun_prop] theorem measurable_sourceRadialDensity (a : Plane → ℝ≥0∞)
    (ha : Measurable a) (x : Plane) : Measurable (sourceRadialDensity a x) := by
  unfold sourceRadialDensity
  have h : Measurable (fun p : ℝ × ℝ =>
    ENNReal.ofReal p.2 * a (x+p.2 • sourceDirection p.1)) := by fun_prop
  exact h.lintegral_prod_right'

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialTestNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable def sourceArcLength : Measure UnitCircle :=
  (volume.restrict (Ioc 0 (2*Real.pi))).map sourceUnitDirection

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ClassPruning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

noncomputable def retainedClassLabels (Q : DyadicSquare) (μ : Measure Plane)
    (N B : ℕ) (t : ℝ≥0∞) : Finset (List ℕ) := by
  classical
  let L := regularizationLeaves Q μ N
  let F := regularizationLabel Q μ N B
  exact (L.image F).filter fun T => t ≤ classMeasure Q μ L F T univ

noncomputable def retainedClassUnion (Q : DyadicSquare) (μ : Measure Plane)
    (N B : ℕ) (t : ℝ≥0∞) : Set Plane :=
  ⋃ T ∈ retainedClassLabels Q μ N B t,
    leafUnion Q (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

noncomputable def finiteMin {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  if h : s.Nonempty then s.inf' h f else 0

def depthPairs (a t Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc a t) ×ˢ (Finset.Icc a t)).filter fun z => z.1 < z.2 ∧ Q ≤ z.2 - z.1

@[simp] theorem mem_depthPairs {a t Q i j : ℕ} :
    (i,j) ∈ depthPairs a t Q ↔ a ≤ i ∧ i < j ∧ j ≤ t ∧ i + Q ≤ j := by
  simp only [depthPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  omega

noncomputable def potential (A : ℕ → ℝ) (a t Q : ℕ) : ℝ :=
  finiteMin (depthPairs a t Q) fun z => A z.1 + A z.2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_Ledger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

noncomputable def intervalMin (A : ℕ → ℝ) (a t : ℕ) : ℝ :=
  finiteMin (Finset.Icc a t) A

noncomputable def height (A : ℕ → ℝ) (a p : ℕ) : ℝ :=
  A p - intervalMin A a p

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualRegularizedClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

structure RegularizedProfileData (Q : DyadicSquare) (ν : Measure Plane)
    (N B : ℕ) (δ lam : ℝ) (m : ℝ → ℝ) : Prop where
  probability : IsProbabilityMeasure ν
  continuous : Continuous m
  zero : m 0 = 0
  slope : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ N → 0 ≤ m v-m u ∧ m v-m u ≤ 2*(v-u)/(N:ℝ)
  affine : ∀ i < N/B+1, ∃ a b : ℝ, ∀ u : ℝ,
    (blockDepth N B (i+1):ℝ) ≤ u → u ≤ (blockDepth N B i:ℝ) → m u = a*u+b
  cells : ∀ n ≤ N, ∀ P : CellPath, P.length = n → 0 < ν (Q.descendant P).carrier →
    ((2:ℝ)^N)^(-3*lam)*((2:ℝ)^N)^(-m n) ≤ (ν (Q.descendant P).carrier).toReal ∧
    (ν (Q.descendant P).carrier).toReal ≤ ((2:ℝ)^N)^(3*lam)*((2:ℝ)^N)^(-m n)
  envelope : ∀ n ≤ N, δ*(n:ℝ)/(N:ℝ)-5*lam ≤ m n-(n:ℝ)/(N:ℝ) ∧
    m n-(n:ℝ)/(N:ℝ) ≤ (n:ℝ)/(N:ℝ)
  adjusted : ∀ u v : ℝ, 0 ≤ u → u ≤ N → 0 ≤ v → v ≤ N →
    |(m v-v/(N:ℝ))-(m u-u/(N:ℝ))| ≤ |v-u|/(N:ℝ)
  packing : ∀ g p : ℕ, g ≤ p → p ≤ N → ∀ x : Plane, ∀ C₀ : ℝ, 0 ≤ C₀ →
    ((occupiedCenterCells Q ν p x (C₀/(2:ℝ)^g)).card:ℝ) ≤
      (4*(C₀/Q.side+1)^2)*((2:ℝ)^N)^(m p-m g+6*lam)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngularRegularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

structure SourceAngularBounds (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) : Prop where
  parallel : ∀ g p : ℕ, g ≤ p → p ≤ N → ∀ P : CellPath, P.length = p →
    sourceArcLength (parallelGoodSet Q ρ g p P
      (2/(2:ℝ)^p*((2:ℝ)^N)^(1000*sig))
      (((2:ℝ)^N)^(height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+2000*(lam+sig))))ᶜ ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig)))
  projection : ∀ p u : ℕ, p ≤ u → u ≤ N → ∀ P : CellPath, P.length = p →
    sourceArcLength (projectionGoodSet Q ρ p u P
      (2/(2:ℝ)^u*((2:ℝ)^N)^(1000*sig))
      (((2:ℝ)^N)^(m u-m p+height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+2000*(lam+sig))))ᶜ ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularWidths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

noncomputable def sourceAngularWidth (N : ℕ) (sig : ℝ) (J i n : ℕ) : ℝ :=
  (2-(i:ℝ)/(J:ℝ))/(2:ℝ)^n*((2:ℝ)^N)^(1000*sig)

noncomputable def sourceAngularRadius (N : ℕ) (sig : ℝ) (l : ℕ) : ℝ :=
  min 1 (1/(2:ℝ)^l*((2:ℝ)^N)^(50*sig))

theorem sourceAngularRadius_pos (N : ℕ) (sig : ℝ) (l : ℕ) :
    0 < sourceAngularRadius N sig l := by unfold sourceAngularRadius; positivity

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngleCoordinateTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceDirection_add_pi (θ : ℝ) :
    sourceDirection (θ+Real.pi) = -sourceDirection θ := by
  simp only [sourceDirection,Real.cos_add_pi,Real.sin_add_pi]
  rw [show ((-(Real.cos θ):ℝ):ℂ)+((-(Real.sin θ):ℝ):ℂ)*Complex.I =
      -((Real.cos θ:ℂ)+(Real.sin θ:ℂ)*Complex.I) by push_cast; ring]
  exact map_neg _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngleMaskDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function ContinuousLinearMap
open scoped Convolution Topology ContDiff

noncomputable def angleDerivativeConstant (j : ℕ) : ℝ :=
  ∫ x : ℝ, ‖iteratedDeriv j ((angleBump 1 zero_lt_one).normed volume) x‖

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngleMasks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

noncomputable def sourceTestMask (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) : ℝ → ℝ :=
  smoothAngleMask (sourceUnitDirection ⁻¹' G) (d/100) (by positivity)

theorem sourceTestMask_contDiff (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    ContDiff ℝ ∞ (sourceTestMask G d hd) := smoothAngleMask_contDiff _ _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialShellMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

/-- The radial shell measure shared by the planar and all-dimensional arguments. -/
noncomputable def sourceAngularShellMeasure (v : ℝ) (Ψ : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun r => ENNReal.ofReal (Ψ (r/(2:ℝ)^v)/(2:ℝ)^v))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_AngularShellEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable def sourceAngularTransform (ρ : Measure Plane) (X : Set Plane) (M : ℝ)
    (b : Plane → UnitCircle → ℂ) (r : ℝ) (ω : UnitCircle) : ℂ :=
  M⁻¹ • ∫ x in X, Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (ω : Plane) x : ℂ)) * b x ω ∂ρ

noncomputable def sourceAngularMoment (U : ℝ × UnitCircle → ℂ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ‖U (r, ω)‖ₑ^2 ∂sourceArcLength

noncomputable def sourceAngularH (a v : ℝ) (Ψ : ℝ → ℝ) (U V : ℝ × UnitCircle → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2:ℝ)^(2*(v-a))) * ∫⁻ r,
    sourceAngularMoment U r * sourceAngularMoment V r ∂sourceAngularShellMeasure v Ψ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleMaskCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

noncomputable def sourceAngle (dir : UnitCircle) : ℝ :=
  Complex.arg (Complex.orthonormalBasisOneI.repr.symm (dir:Plane))

@[fun_prop] theorem measurable_sourceAngle : Measurable sourceAngle := by
  unfold sourceAngle
  exact Complex.measurable_arg.comp
    (Complex.orthonormalBasisOneI.repr.symm.continuous.measurable.comp continuous_subtype_val.measurable)

theorem sourceUnitDirection_sourceAngle (dir : UnitCircle) :
    sourceUnitDirection (sourceAngle dir) = dir := by
  apply Subtype.ext
  let z := Complex.orthonormalBasisOneI.repr.symm (dir:Plane)
  have hn : ‖z‖ = 1 := (Complex.orthonormalBasisOneI.repr.symm.norm_map _).trans dir.property
  have hc := Complex.norm_mul_cos_arg z
  have hs := Complex.norm_mul_sin_arg z
  rw [hn,one_mul] at hc hs
  change Complex.orthonormalBasisOneI.repr
    ((Real.cos (Complex.arg z):ℂ)+(Real.sin (Complex.arg z):ℂ)*Complex.I) = _
  rw [hc,hs,Complex.re_add_im]
  exact Complex.orthonormalBasisOneI.repr.apply_symm_apply _

noncomputable def circleTestMask (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) : UnitCircle → ℝ :=
  fun dir => sourceTestMask G d hd (sourceAngle dir)

@[fun_prop] theorem measurable_circleTestMask (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    Measurable (circleTestMask G d hd) :=
  (sourceTestMask_contDiff G d hd).continuous.measurable.comp measurable_sourceAngle

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleMaskSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

noncomputable def circleAntipode (dir : UnitCircle) : UnitCircle :=
  ⟨-(dir:Plane),by simpa using dir.property⟩

theorem sourceUnitDirection_add_pi (θ : ℝ) :
    sourceUnitDirection (θ+Real.pi) = circleAntipode (sourceUnitDirection θ) := by
  apply Subtype.ext
  exact sourceDirection_add_pi θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SpatialAnchorMasks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

noncomputable def occupiedAnchorPaths (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ) : Finset CellPath := by
  classical
  exact (dyadicPaths n).filter fun P => 0 < ρ (Q.descendant P).carrier

noncomputable def spatialAnchorMask (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) (dir : UnitCircle) : ℝ := by
  classical
  exact ∑ P ∈ occupiedAnchorPaths Q ρ n,
    if x ∈ (Q.descendant P).carrier then circleTestMask (G P) d hd dir else 0

@[fun_prop] theorem measurable_spatialAnchorMask (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    Measurable (fun z : Plane × UnitCircle => spatialAnchorMask Q ρ n G d hd z.1 z.2) := by
  classical
  apply Finset.measurable_sum
  intro P _
  exact Measurable.ite ((Q.descendant P).measurable.preimage measurable_fst)
    ((measurable_circleTestMask _ _ _).comp measurable_snd) measurable_const

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_InteriorPolicy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def finiteArgmin (S : Finset ℕ) (f : ℕ → ℝ) : ℕ :=
  if h : S.Nonempty then Classical.choose (Finset.exists_mem_eq_inf' h f) else 0

def policyBlock (N q k : ℕ) : Finset ℕ := Finset.Ico (k*q) (min ((k+1)*q) (N+1))

noncomputable def policyRepresentative (A : ℕ → ℝ) (N q k : ℕ) : ℕ :=
  finiteArgmin (policyBlock N q k) A

def policyBlocks (N q a t : ℕ) : Finset ℕ :=
  (Finset.range (N/q+1)).filter fun k => a+q ≤ k*q ∧ (k+1)*q ≤ t-q+1

noncomputable def policyKey (A : ℕ → ℝ) (N q a t : ℕ) : ℕ :=
  finiteArgmin (policyBlocks N q a t) (fun k => A (policyRepresentative A N q k))

noncomputable def policyDepth (A : ℕ → ℝ) (N q a t : ℕ) : ℕ :=
  policyRepresentative A N q (policyKey A N q a t)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PolicyDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

inductive PolicyDescriptor where
  | parallel (g p : ℕ)
  | projection (p u : ℕ)
  deriving DecidableEq

def descriptorAnchor : PolicyDescriptor → ℕ
  | .parallel _ p => p
  | .projection p _ => p

def descriptorLength : PolicyDescriptor → ℕ
  | .parallel g p => p-g
  | .projection p u => u-p

noncomputable def originDescriptors (A : ℕ → ℝ) (N q b u : ℕ) : Finset PolicyDescriptor :=
  let p := policyDepth A N q b u
  let l := min (p-b) (u-p)
  (Finset.Ico (p-l) p).image (fun g => PolicyDescriptor.parallel g p) ∪
    if b+u < 2*p then {PolicyDescriptor.projection p u} else ∅

def policyOrigins (N q a t : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N+1)).product (Finset.range (N+1))).filter fun z =>
    a ≤ z.1 ∧ z.2 ≤ t ∧ z.1+100*q < z.2

noncomputable def policyDescriptorList (A : ℕ → ℝ) (N q a t : ℕ) : Finset PolicyDescriptor :=
  (policyOrigins N q a t).biUnion (fun z => originDescriptors A N q z.1 z.2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_DescriptorMasks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

def ValidDescriptor (N : ℕ) : PolicyDescriptor → Prop
  | .parallel g p => g ≤ p ∧ p ≤ N
  | .projection p u => p ≤ u ∧ u ≤ N

noncomputable def descriptorGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath) : PolicyDescriptor → Set UnitCircle
  | .parallel g p => parallelGoodSet Q ρ g p P (sourceAngularWidth N sig J i p)
      (((2:ℝ)^N)^(height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+2000*(lam+sig)))
  | .projection p u => projectionGoodSet Q ρ p u P (sourceAngularWidth N sig J i u)
      (((2:ℝ)^N)^(m u-m p+height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+2000*(lam+sig)))

noncomputable def descriptorSpatialMask (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) : Plane → UnitCircle → ℝ :=
  spatialAnchorMask Q ρ (descriptorAnchor b) (fun P => descriptorGoodSet Q ρ m N lam sig J i P b)
    (sourceAngularRadius N sig (descriptorLength b)) (sourceAngularRadius_pos _ _ _)

noncomputable def descriptorListMask (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (S : Finset PolicyDescriptor)
    (x : Plane) (dir : UnitCircle) : ℝ :=
  ∏ b ∈ S, descriptorSpatialMask Q ρ m N lam sig J i b x dir

@[fun_prop] theorem measurable_descriptorSpatialMask (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) :
    Measurable (fun z : Plane × UnitCircle => descriptorSpatialMask Q ρ m N lam sig J i b z.1 z.2) :=
  measurable_spatialAnchorMask _ _ _ _ _ _

@[fun_prop] theorem measurable_descriptorListMask (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (S : Finset PolicyDescriptor) :
    Measurable (fun z : Plane × UnitCircle => descriptorListMask Q ρ m N lam sig J i S z.1 z.2) := by
  apply Finset.measurable_prod
  intro b _
  exact measurable_descriptorSpatialMask _ _ _ _ _ _ _ _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_NormalizedSymbolFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

noncomputable def symbolDerivativeConstant (B : ℕ) : ℝ :=
  1 + ∑ n ∈ Finset.range (B+1), (100:ℝ)^n * angleDerivativeConstant n

noncomputable def normalizedMaskFactor (w : ℝ → ℝ) (d : ℝ) (k : ℕ) : ℝ → ℝ :=
  fun θ => d^k * iteratedDeriv k w θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InheritedAngularSymbols
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

noncomputable def descriptorAngleMask (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) : ℝ → ℝ :=
  fun θ => descriptorSpatialMask Q ρ m N lam sig J i b x (sourceUnitDirection θ)

noncomputable def inheritedMaskProduct {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane) : ℝ → ℝ :=
  fun θ => ∏ a ∈ S, normalizedMaskFactor
    (descriptorAngleMask Q ρ m N lam sig J i (b a) (x a))
    (sourceAngularRadius N sig (descriptorLength (b a))) (k a) θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularEnergyDropping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable def inheritedCircleSymbol {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane) (ω : UnitCircle) : ℂ :=
  h x * (inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x) (sourceAngle ω):ℂ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_QuadraticStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable def fresnelCoefficient (b : ℝ) : ℂ :=
  (((Real.pi/b)^(1/2:ℝ):ℝ):ℂ)*Complex.exp (-(Real.pi:ℂ)/4*Complex.I)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationarySineChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def stationarySineChart (θ : ℝ) : ℝ := 2 * Real.sin (θ / 2)
noncomputable def stationarySineInverse (u : ℝ) : ℝ := 2 * Real.arcsin (u / 2)
noncomputable def stationarySineJacobian (u : ℝ) : ℝ := (Real.sqrt (1 - u^2/4))⁻¹

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryChartCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

noncomputable def stationaryCutoff : ContDiffBump (0:ℝ) :=
  ⟨1/2,1,by norm_num,by norm_num⟩
noncomputable def stationaryChartCutoff : ContDiffBump (0:ℝ) :=
  ⟨1,3/2,by norm_num,by norm_num⟩

noncomputable def extendedStationaryInverse (u : ℝ) : ℝ :=
  stationaryChartCutoff u * stationarySineInverse u
noncomputable def stationaryWeight (u : ℝ) : ℝ :=
  stationaryCutoff u * stationarySineJacobian u

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryChartAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff SchwartzMap

noncomputable def stationaryAmplitude (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (stationaryWeight u : ℂ) * f (extendedStationaryInverse u)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_LocalizedStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

noncomputable def stationaryDerivativeExpansion (f : ℝ → ℂ) (n : ℕ) (Λ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1),
    ((((k.factorial:ℝ)⁻¹*(Real.pi^2/(Λ/2))^k):ℝ):ℂ)*Complex.I^k *
      (((-2*(Real.pi:ℂ)*Complex.I)^(2*k))⁻¹ * iteratedDeriv (2*k) (stationaryAmplitude f) 0)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularIntegrationByParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def angularTransport (q f : ℝ → ℂ) : ℝ → ℂ :=
  deriv (fun x => q x * f x)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularTransportBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

noncomputable def angularTransportIterate (q : ℝ → ℂ) : ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0, f => f
  | n+1, f => deriv (fun x => q x * angularTransportIterate q n f x)

noncomputable def angularTransportCost (q : ℝ → ℂ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 1
  | n+1, m, x => ∑ k ∈ Finset.range (m+2),
      ((m+1).choose k:ℝ) * ‖iteratedDeriv k q x‖ * angularTransportCost q n (m+1-k) x

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_FullCircleStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def fullCircleStationaryExpansion (Λ : ℝ) (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  Complex.exp (Complex.I*(Λ:ℂ))*(fresnelCoefficient (Λ/2)*stationaryDerivativeExpansion f n Λ) +
    conj (Complex.exp (Complex.I*(Λ:ℂ))*(fresnelCoefficient (Λ/2)*
      stationaryDerivativeExpansion (fun θ => conj (f (θ+Real.pi))) n Λ))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularBinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff Topology

noncomputable def angularBinKernel (t : ℝ) : ℝ :=
  Real.smoothTransition (t+1) - Real.smoothTransition t

theorem angularBinKernel_zero_left {t : ℝ} (ht : t ≤ -1) : angularBinKernel t = 0 := by
  unfold angularBinKernel
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_self]

theorem angularBinKernel_zero_right {t : ℝ} (ht : 1 ≤ t) : angularBinKernel t = 0 := by
  unfold angularBinKernel
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le ht, sub_self]

theorem angularBinKernel_tsupport : tsupport angularBinKernel ⊆ Icc (-1 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  constructor
  · by_contra h
    exact ht (angularBinKernel_zero_left (le_of_not_ge h))
  · by_contra h
    exact ht (angularBinKernel_zero_right (le_of_not_ge h))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularBinSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set Filter
open scoped ContDiff Topology

noncomputable def angularBinSelection (p : ℤ → Prop) (t : ℝ) : ℝ := by
  classical
  exact ∑' k : ℤ, if p k then angularBinKernel (t-k) else 0

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_PeriodicAngularBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set
open scoped ContDiff Topology

noncomputable def periodicAngularBin (n j : ℕ) (θ : ℝ) : ℝ :=
  angularBinSelection (fun k => (k % (n : ℤ)).toNat = j) ((n : ℝ)/(2*Real.pi)*θ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SelectedAngularBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open scoped ContDiff Topology

noncomputable def angularBinCount (δ : ℝ) : ℕ := ⌈2*Real.pi/δ⌉₊

theorem angularBinCount_pos {δ : ℝ} (hδ : 0 < δ) : 0 < angularBinCount δ := by
  exact Nat.ceil_pos.mpr (by positivity)

theorem angularBinCount_bounds {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 2*Real.pi) :
    2*Real.pi/(angularBinCount δ : ℝ) ≤ δ ∧
      (angularBinCount δ : ℝ)/(2*Real.pi) ≤ 2/δ := by
  have hn : (0 : ℝ) < angularBinCount δ := by exact_mod_cast angularBinCount_pos hδ
  have hlo := Nat.le_ceil (2*Real.pi/δ)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 2*Real.pi/δ by positivity)
  change 2*Real.pi/δ ≤ (angularBinCount δ : ℝ) at hlo
  change (angularBinCount δ : ℝ) < 2*Real.pi/δ+1 at hhi
  constructor
  · apply (div_le_iff₀ hn).mpr
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hlo
  · apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    have hbase : 1 ≤ 2*Real.pi/δ := (le_div_iff₀ hδ).mpr (by simpa using hcap)
    calc
      _ ≤ 2*(2*Real.pi/δ) := by linarith
      _ = _ := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryArcLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

 theorem sourceUnitDirection_periodic : Function.Periodic sourceUnitDirection (2*Real.pi) := by
  intro θ
  rw [show θ+2*Real.pi = (θ+Real.pi)+Real.pi by ring,
    sourceUnitDirection_add_pi,sourceUnitDirection_add_pi]
  apply Subtype.ext
  simp [circleAntipode]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleAngularBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

noncomputable def circleAngularBin (n j : ℕ) (dir : UnitCircle) : ℝ :=
  periodicAngularBin n j (sourceAngle dir)

 theorem angularBinSelection_witness (p : ℤ → Prop) (t : ℝ)
    (h : angularBinSelection p t ≠ 0) : ∃ k : ℤ, p k ∧ |t-k| ≤ 1 := by
  classical
  have he : ∃ k : ℤ, (if p k then angularBinKernel (t-k) else 0) ≠ 0 := by
    by_contra hh
    push Not at hh
    exact h (by unfold angularBinSelection; simp only [hh, tsum_zero])
  obtain ⟨k,hk⟩ := he
  by_cases hp : p k
  · simp only [hp, ↓reduceIte] at hk
    have hs := angularBinKernel_tsupport (subset_closure hk)
    exact ⟨k,hp,abs_le.mpr hs⟩
  · simp [hp] at hk

 theorem angularBin_center_residue {n : ℕ} (hn : 0 < n) (j : ℕ) (k : ℤ)
    (hk : (k % (n : ℤ)).toNat = j) :
    sourceUnitDirection (2*Real.pi/(n : ℝ)*(k : ℝ)) =
      sourceUnitDirection (2*Real.pi/(n : ℝ)*(j : ℝ)) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn'.ne'
  have hr : k % (n : ℤ) = (j : ℤ) := by
    rw [← hk, Int.toNat_of_nonneg (Int.emod_nonneg k hn'.ne')]
  have he : (k : ℝ) = (j : ℝ)+(n : ℝ)*(k/(n : ℤ) : ℤ) := by
    exact_mod_cast (show k = (j : ℤ)+(n : ℤ)*(k/(n : ℤ)) by
      rw [← hr]; exact (Int.emod_add_mul_ediv k (n : ℤ)).symm)
  rw [he, show 2*Real.pi/(n : ℝ)*((j : ℝ)+(n : ℝ)*(k/(n : ℤ) : ℤ)) =
      2*Real.pi/(n : ℝ)*(j : ℝ)+(k/(n : ℤ) : ℤ)*(2*Real.pi) by field_simp]
  exact sourceUnitDirection_periodic.int_mul (k/(n : ℤ)) _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularLabelEligibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def AngularLabelEligible (ρ : Measure Plane) (X : Set Plane)
    (b : Plane → UnitCircle → ℂ) (n j : ℕ) : Prop :=
  ∃ ω ∈ tsupport (circleAngularBin n j), ¬ ∀ᵐ x ∂ρ.restrict X, b x ω = 0

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDifferentialExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

inductive AngularDifferentialExpr where
  | term (coefficient : ℂ) (order : ℕ)
  | add (p q : AngularDifferentialExpr)
  | comp (p q : AngularDifferentialExpr)

namespace AngularDifferentialExpr

def order : AngularDifferentialExpr → ℕ
  | .term _ k => k
  | .add p q => max p.order q.order
  | .comp p q => p.order + q.order

noncomputable def apply : AngularDifferentialExpr → (ℝ → ℂ) → (ℝ → ℂ)
  | .term c k, f => fun x => c * iteratedDeriv k f x
  | .add p q, f => fun x => p.apply f x + q.apply f x
  | .comp p q, f => p.apply (q.apply f)

noncomputable def cost : AngularDifferentialExpr → ℝ
  | .term c _ => ‖c‖
  | .add p q => p.cost + q.cost
  | .comp p q => p.cost * q.cost

def sum : List AngularDifferentialExpr → AngularDifferentialExpr
  | [] => .term 0 0
  | p :: ps => .add p (sum ps)

end AngularDifferentialExpr
end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryDifferentialExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

noncomputable def angularFiniteSum {α : Type*} (s : Finset α)
    (p : α → AngularDifferentialExpr) : AngularDifferentialExpr :=
  AngularDifferentialExpr.sum (s.toList.map p)

noncomputable def stationaryLeadingConstant : ℂ :=
  (Real.sqrt (2*Real.pi):ℂ) * Complex.exp (-(Real.pi:ℂ)/4*Complex.I)

noncomputable def stationaryJetExpr (n : ℕ) : AngularDifferentialExpr :=
  angularFiniteSum (Finset.range (n+1)) (fun k =>
    angularFiniteSum Finset.univ (fun c : OrderedFinpartition (n-k) =>
      .term ((n.choose k:ℂ) * iteratedDeriv k (fun u => (stationaryWeight u:ℂ)) 0 *
        ((∏ j, iteratedDeriv (c.partSize j) extendedStationaryInverse 0:ℝ):ℂ)) c.length))

noncomputable def directStationaryExpr (j : ℕ) : AngularDifferentialExpr :=
  .comp (.term (stationaryLeadingConstant * (((j.factorial:ℝ)⁻¹:ℝ):ℂ) *
    (-Complex.I/2)^j) 0) (stationaryJetExpr (2*j))

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

noncomputable def inverseStationaryExpr : ℕ → AngularDifferentialExpr
  | 0 => .term stationaryLeadingConstant⁻¹ 0
  | n+1 => .comp (.term (-stationaryLeadingConstant⁻¹) 0)
      (angularFiniteSum (Finset.range (n+1)) (fun k =>
        .comp (directStationaryExpr (k+1)) (inverseStationaryExpr (n-k))))
termination_by n => n
decreasing_by omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_InactiveBinGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set Metric
open scoped ContDiff Topology

def AngularBinActive (n j : ℕ) (e : UnitCircle) (radius : ℝ) : Prop :=
  ∃ dir ∈ tsupport (circleAngularBin n j), dist e dir < radius

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def sourceCircleRotate (axis : ℝ) (dir : UnitCircle) : UnitCircle :=
  sourceUnitDirection (sourceAngle dir + axis)

@[simp] theorem sourceCircleRotate_zero (dir : UnitCircle) : sourceCircleRotate 0 dir = dir := by
  simp only [sourceCircleRotate, add_zero, sourceUnitDirection_sourceAngle]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable def sourcePlaneWave (r : ℝ) (ω : UnitCircle) (x : Plane) : ℂ :=
  Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (ω : Plane) x : ℂ))

noncomputable def sourceDistanceF (ψ : UnitCircle → ℂ)
    (U V : ℝ × UnitCircle → ℂ) (r : ℝ) : ℂ :=
  ∫ ω, ψ ω * U (r,ω) * conj (V (r,ω)) ∂sourceArcLength

noncomputable def sourceDistanceHF (a v : ℝ) (Ψ : ℝ → ℝ)
    (ψ : UnitCircle → ℂ) (U V : ℝ × UnitCircle → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2:ℝ)^(2*(v-a))) *
    ∫⁻ r, ‖sourceDistanceF ψ U V r‖ₑ^2 ∂sourceAngularShellMeasure v Ψ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceFormFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def sourceDistanceKernel (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (r : ℝ) (x y : Plane) : ℂ :=
  ∫ ω, sourcePlaneWave r ω (x-y) * (ψ ω * b₁ x ω * conj (b₂ y ω)) ∂sourceArcLength

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

noncomputable def graphConeBump : ContDiffBump (0 : ℝ) :=
  ⟨1/10, 1/5, by norm_num, by norm_num⟩

noncomputable def graphConeCutoff (θ : ℝ) : ℂ := (graphConeBump θ : ℝ)

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

noncomputable def sourceConeCircle (axis : ℝ) (dir : UnitCircle) : ℂ :=
  graphConeCutoff (sourceAngle (sourceCircleRotate (-axis) dir))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphCoordinateInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def graphChartZ (u v : Plane) : ℝ :=
  planeDot (u-v) (quarterTurn (u+v))/‖u+v‖^2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphSignPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

noncomputable def graphSignPlus (p : Plane × Plane) : ℝ :=
  Real.smoothTransition ((‖p.1+p.2‖^2-1)/2)

noncomputable def graphSignMinus (p : Plane × Plane) : ℝ := 1-graphSignPlus p

noncomputable def circleGraphSignPlus (p : UnitCircle × UnitCircle) : ℝ :=
  graphSignPlus (p.1, p.2)

noncomputable def circleGraphSignMinus (p : UnitCircle × UnitCircle) : ℝ :=
  graphSignMinus (p.1, p.2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphEndpointContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def graphBinWeight (n j k : ℕ) (p : UnitCircle × UnitCircle) : ℝ :=
  circleAngularBin n j p.1 * circleAngularBin n k p.2

noncomputable def graphDistanceWeight (axis : ℝ) (n j k : ℕ)
    (p : UnitCircle × UnitCircle) : ℂ :=
  (graphBinWeight n j k p : ℂ) * sourceConeCircle axis p.1 * conj (sourceConeCircle axis p.2)

noncomputable def graphProductWeight (plus : Bool) (n j k : ℕ)
    (p : UnitCircle × UnitCircle) : ℂ :=
  ((graphBinWeight n j k p *
    (if plus then circleGraphSignPlus p else circleGraphSignMinus p)) : ℝ)

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

abbrev GraphLiftSpace := Fin 3 → ℝ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_GraphFourPointKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def graphFourAmplitude (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane)
    (u v : UnitCircle) : ℂ :=
  W (u,v) * (b 0 (x 0) u * conj (b 1 (x 1) u)) *
    (b 2 (x 2) v * conj (b 3 (x 3) v))

noncomputable def graphFourKernel (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane)
    (r : ℝ) (u v : UnitCircle) : ℂ :=
  (sourcePlaneWave r u (x 0-x 1) * sourcePlaneWave r v (x 2-x 3)) *
    graphFourAmplitude b W x u v

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphChartVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

noncomputable def graphChartAxis (u v : Plane) : Plane := ‖u+v‖⁻¹ • (u+v)

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

noncomputable def graphUncappedAngularScale (N : ℕ) (sig t : ℝ) : ℝ :=
  (2 : ℝ)^(-t) * ((2 : ℝ)^N)^(10*sig)

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

noncomputable def graphRotatedDistanceWeight (axis : ℝ) (n j k : ℕ)
    (p : UnitCircle × UnitCircle) : ℂ :=
  graphDistanceWeight 0 n j k (sourceCircleRotate (-axis) p.1, sourceCircleRotate (-axis) p.2)

noncomputable def graphSourceWeight (distance plus : Bool) (axis : ℝ) (n j k : ℕ) :
    UnitCircle × UnitCircle → ℂ :=
  if distance then graphRotatedDistanceWeight axis n j k else graphProductWeight plus n j k

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_GraphFourSymbolDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

def graphSmoothDomain : Set (Plane × ℝ) := {p | p.1 ≠ 0}

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphDerivativeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Filter
open scoped ContDiff Topology ComplexConjugate

structure GraphDerivativeBound (n : ℕ) (f : (Plane × ℝ) → ℂ) (C D : ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ f graphSmoothDomain
  bound : ∀ j ≤ n, ∀ (η : Plane) (z : ℝ), ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ →
    ‖iteratedFDeriv ℝ j f (η,z)‖ ≤ C*D^j

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphNonedgeIndexCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

abbrev GraphCellQuadIndex := (CellPath × CellPath) × (CellPath × CellPath)
abbrev GraphNonedgeIndex := GraphCellQuadIndex × ((ℕ × ℕ) × Bool)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphActualQuadCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def graphQuadPath (q : GraphCellQuadIndex) (l : Fin 4) : CellPath :=
  ![q.1.1,q.1.2,q.2.1,q.2.2] l

noncomputable def graphQuadCells (Q : Fin 4 → DyadicSquare) (q : GraphCellQuadIndex) (l : Fin 4) : DyadicSquare :=
  (Q l).descendant (graphQuadPath q l)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphCompleteWeightSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ComplexConjugate

def graphSourceSign (distance plus : Bool) : ℝ :=
  if distance then 1 else if plus then 1 else -1

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphAmplitudeRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

def GraphSourceRepresentative (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    (q : UnitCircle × UnitCircle) : Prop :=
  q ∈ tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k) ∧
    ∀ w ∈ tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k),
    |graphChartZ (w.1:Plane) (graphSourceSign distance plus • (w.2:Plane))-
      graphChartZ (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))|+
    dist (graphChartAxis (w.1:Plane) (graphSourceSign distance plus • (w.2:Plane)))
      (graphChartAxis (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))) ≤ 112*δ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphActualNonedgeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

noncomputable def graphNonedgeThreshold (N : ℕ) (sig p : ℝ) : ℝ :=
  (2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig)

noncomputable def graphRepresentativeZ (distance plus : Bool) (q : UnitCircle × UnitCircle) : ℝ :=
  graphChartZ (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))

noncomputable def graphRepresentativeAxis (distance plus : Bool) (q : UnitCircle × UnitCircle) : Plane :=
  graphChartAxis (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphNonedgeIntegralErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def GraphNonedge (N : ℕ) (sig p s z₀ : ℝ) (e₀ v₀ w₀ : Plane) : Prop :=
  graphNonedgeThreshold N sig p < ‖graphA z₀ v₀+s • graphB z₀ w₀‖ ∨
    graphNonedgeThreshold N sig p < |inner ℝ e₀ (graphDerivative s v₀ w₀)|

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_EligibleProductGraphSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

def graphProductSlotBin (j k : ℕ) (l : Fin 4) : ℕ := ![j,j,k,k] l

def GraphProductEligible (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (m j k : ℕ) : Prop :=
  ∀ l, AngularLabelEligible (ρ l) (X l) (b l) m (graphProductSlotBin j k l)

def GraphProductIndexEligible (ρ : Fin 4 → Measure Plane) (Q : Fin 4 → DyadicSquare)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (m : ℕ) (e : GraphNonedgeIndex) : Prop :=
  GraphProductEligible ρ (fun l => (graphQuadCells Q e.1 l).carrier) b m e.2.1.1 e.2.1.2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphRetainedEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

def GraphRetainedEdge (N : ℕ) (sig p : ℝ) (distance plus : Bool)
    (P : Fin 4 → DyadicSquare) (q : UnitCircle × UnitCircle) : Prop :=
  ‖graphA (graphRepresentativeZ distance plus q) ((P 0).center-(P 1).center)+
    graphSourceSign distance plus • graphB (graphRepresentativeZ distance plus q) ((P 2).center-(P 3).center)‖ ≤
      graphNonedgeThreshold N sig p ∧
  (distance = false → |inner ℝ (graphRepresentativeAxis distance plus q)
    (graphDerivative (graphSourceSign distance plus) ((P 0).center-(P 1).center)
      ((P 2).center-(P 3).center))| ≤ graphNonedgeThreshold N sig p)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProductMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def productMatrixIndex (row col : CellPath × CellPath) (j b : ℕ) (plus : Bool) : GraphNonedgeIndex :=
  (((row.1,col.1),(row.2,col.2)),((j,b),plus))

noncomputable def productMatrixNeighbors (I : Finset GraphNonedgeIndex) (p j b : ℕ)
    (plus reverse : Bool) (row : CellPath × CellPath) : Finset (CellPath × CellPath) := by
  classical
  exact ((dyadicPaths p) ×ˢ (dyadicPaths p)).filter (fun col =>
    (if reverse then productMatrixIndex col row j b plus else productMatrixIndex row col j b plus) ∈ I)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ActualProductDegrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def activeProductMatrixNeighbors (I : Finset GraphNonedgeIndex)
    (p j b : ℕ) (θ : ℝ) (plus reverse : Bool) (row : CellPath × CellPath) :
    Finset (CellPath × CellPath) := by
  classical
  exact if (tsupport (graphSourceWeight false plus 0 (angularBinCount θ) j b)).Nonempty
    then productMatrixNeighbors I p j b plus reverse row else ∅

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProductOccupiedVertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def sourceProductVertices (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (n : ℕ) : Finset (CellPath × CellPath) :=
  ((occupiedAnchorPaths (Q₁.descendant A) ρ n).image (fun c => A++c)) ×ˢ
    ((occupiedAnchorPaths (Q₂.descendant B) ν n).image (fun c => B++c))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularNearNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

def angularNear (Q₁ Q₂ : DyadicSquare) (p : ℕ)
    (row col : CellPath × CellPath) : Prop :=
  dist (Q₁.descendant row.1).center (Q₁.descendant col.1).center ≤ 20/(2:ℝ)^p ∧
  dist (Q₂.descendant row.2).center (Q₂.descendant col.2).center ≤ 20/(2:ℝ)^p

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularLengthPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

def angularLengthLeft : Set (Fin 4 → Plane) :=
  {x | 2*dist (x 2) (x 3) < dist (x 0) (x 1)}

def angularLengthRight : Set (Fin 4 → Plane) :=
  {x | 2*dist (x 0) (x 1) < dist (x 2) (x 3)}

def angularLengthComparable : Set (Fin 4 → Plane) :=
  {x | dist (x 0) (x 1) ≤ 2*dist (x 2) (x 3) ∧
    dist (x 2) (x 3) ≤ 2*dist (x 0) (x 1)}

noncomputable def angularLengthShell (b : ℕ) : Set (Fin 4 → Plane) :=
  angularLengthComparable ∩ {x |
    512*(2:ℝ)^(-(b:ℝ)) < max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ∧
    max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 1024*(2:ℝ)^(-(b:ℝ))}

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularKernelIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def angularKernelIntegral (a v : ℝ) (Ψ : ℝ → ℝ)
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) : ℂ :=
  ((2:ℝ)^(2*(v-a))) • ∫ z, F z
    ∂((sourceAngularShellMeasure v Ψ).prod (sourceArcLength.prod sourceArcLength))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularNearSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

noncomputable def angularPairTerm (U V : CellPath → ℂ) (row col : CellPath × CellPath) : ℂ :=
  (U row.1 * conj (U col.1)) * (V row.2 * conj (V col.2))

noncomputable def angularRestrictedSum (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (U V : CellPath → ℂ) : ℂ :=
  ∑ row ∈ C, ∑ col ∈ C, if G row col then angularPairTerm U V row col else 0

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularRestrictedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

noncomputable def angularRestrictedKernel (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (U V : CellPath → ℝ × UnitCircle → ℂ) (z : ℝ × (UnitCircle × UnitCircle)) : ℂ :=
  angularRestrictedSum C G (fun P => U P (z.1,z.2.1)) (fun Q => V Q (z.1,z.2.2))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularCellKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def angularCellTransform (Q : DyadicSquare) (ρ : Measure Plane)
    (M : ℝ) (β : Plane → UnitCircle → ℂ) (P : CellPath) (z : ℝ × UnitCircle) : ℂ :=
  sourceAngularTransform ρ (Q.descendant P).carrier M β z.1 z.2

noncomputable def angularCellContribution (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (n : ℕ) (a v : ℝ) (Ψ : ℝ → ℝ)
    (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (β γ : Plane → UnitCircle → ℂ)
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop) : ℂ :=
  ((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2) • angularKernelIntegral a v Ψ
    (angularRestrictedKernel (sourceProductVertices Q₁ Q₂ ρ ν A B n) G
      (angularCellTransform Q₁ ρ Mp₁ β) (angularCellTransform Q₂ ν Mp₂ γ))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularCellSpatialIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def angularCellSpatialIntegral (Q₁ Q₂ : DyadicSquare)
    (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (row col : CellPath × CellPath) (v : ℝ) (Ψ : ℝ → ℝ) : ℂ :=
  ∫ x, ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
    graphFourKernel ![β,β,γ,γ] (fun _ => 1) x r u w
      ∂sourceArcLength ∂sourceArcLength)
    ∂Measure.pi (fun i => (![ρ,ρ,ν,ν] i).restrict
      (![ (Q₁.descendant row.1).carrier, (Q₁.descendant col.1).carrier,
          (Q₂.descendant row.2).carrier, (Q₂.descendant col.2).carrier] i))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularPairCircleIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def angularPairCircleIntegral (β : Plane → UnitCircle → ℂ)
    (x y : Plane) (r : ℝ) : ℂ :=
  ∫ u, sourcePlaneWave r u (x-y) * (β x u*conj (β y u)) ∂sourceArcLength

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularOriginalIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def angularOriginalSpatialKernel (β γ : Plane → UnitCircle → ℂ)
    (v : ℝ) (Ψ : ℝ → ℝ) (x : Fin 4 → Plane) : ℂ :=
  ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
    (angularPairCircleIntegral β (x 0) (x 1) r *
     angularPairCircleIntegral γ (x 2) (x 3) r))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularOriginalFarPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def angularFourCellMeasure (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (row col : CellPath × CellPath) : Measure (Fin 4 → Plane) :=
  Measure.pi (fun i => (![ρ,ρ,ν,ν] i).restrict
    (![(Q₁.descendant row.1).carrier,(Q₁.descendant col.1).carrier,
       (Q₂.descendant row.2).carrier,(Q₂.descendant col.2).carrier] i))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ParentConeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

noncomputable def sourceParentAxis (P Q : DyadicSquare) : ℝ :=
  sourceAngle (sourceRadialUnit Q.center P.center)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ParentRetainedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def sourceParentDistanceF (X Y : DyadicSquare) (ρ ν : Measure Plane)
    (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) : ℝ → ℂ :=
  sourceDistanceF (sourceConeCircle (sourceParentAxis X Y))
    (fun z => sourceAngularTransform ρ X.carrier M₁ b₁ z.1 z.2)
    (fun z => sourceAngularTransform ν Y.carrier M₂ b₂ z.1 z.2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialFailureMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal

@[fun_prop] theorem measurable_sourceRadialUnit_joint :
    Measurable (fun z : Plane × Plane => sourceRadialUnit z.1 z.2) := by
  apply Measurable.subtype_mk
  change Measurable (fun z : Plane × Plane => sourceRadialVector z.1 z.2)
  unfold sourceRadialVector
  apply Measurable.ite (isClosed_eq continuous_snd continuous_fst).measurableSet measurable_const
  fun_prop

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularStationarySpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def angularPairAngle (x y : Plane) : ℝ :=
  sourceAngle (sourceRadialUnit y x)

noncomputable def angularPairStationary (β : Plane → UnitCircle → ℂ)
    (n : ℕ) (x y : Plane) (r : ℝ) : ℂ :=
  fullCircleStationaryExpansion (r*‖x-y‖)
    (fun t => β x (sourceUnitDirection (t+angularPairAngle x y))*
      conj (β y (sourceUnitDirection (t+angularPairAngle x y)))) n

noncomputable def angularStationarySpatialKernel (β γ : Plane → UnitCircle → ℂ)
    (n : ℕ) (v : ℝ) (Ψ : ℝ → ℝ) (x : Fin 4 → Plane) : ℂ :=
  ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
    (angularPairStationary β n (x 0) (x 1) r * angularPairStationary γ n (x 2) (x 3) r))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualSingleStationaryKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def angularSingleStationaryKernel (β γ : Plane → UnitCircle → ℂ)
    (n : ℕ) (v : ℝ) (Ψ : ℝ → ℝ) (x : Fin 4 → Plane) : ℂ :=
  ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
    (angularPairStationary β n (x 0) (x 1) r *
      angularPairCircleIntegral γ (x 2) (x 3) r))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularFourCellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

instance angularFourCellMeasure_finite (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (row col : CellPath × CellPath) :
    IsFiniteMeasure (angularFourCellMeasure Q₁ Q₂ ρ ν row col) := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  exact inferInstanceAs (IsFiniteMeasure (Measure.pi (fun i => (ρs i).restrict
    (![(Q₁.descendant row.1).carrier,(Q₁.descendant col.1).carrier,
       (Q₂.descendant row.2).carrier,(Q₂.descendant col.2).carrier] i))))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_OrderedLeibniz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

noncomputable def orderedDerivAssignments {ι : Type*} [DecidableEq ι]
    (S : Finset ι) : ℕ → List (ι → ℕ)
  | 0 => [fun _ => 0]
  | n+1 => (orderedDerivAssignments S n).flatMap
      (fun k => S.toList.map (fun i => Function.update k i (k i+1)))

noncomputable def assignedDerivProduct {ι : Type*} (S : Finset ι)
    (f : ι → ℝ → ℂ) (k : ι → ℕ) : ℝ → ℂ :=
  fun x => ∏ i ∈ S, iteratedDeriv (k i) (f i) x

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularOperatorTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff
namespace AngularDifferentialExpr

noncomputable def terms : AngularDifferentialExpr → List (ℂ × ℕ)
  | .term c k => [(c,k)]
  | .add p q => p.terms ++ q.terms
  | .comp p q => p.terms.flatMap (fun a => q.terms.map (fun b => (a.1*b.1,a.2+b.2)))

end AngularDifferentialExpr

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ProductEnergyMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal NNReal

noncomputable def finiteEnergyMaximum {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞) : ℝ :=
  ((S.sup (fun i => (E i).toNNReal) : ℝ≥0) : ℝ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_InheritedPolicyState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def remainingPolicyDescriptors (A : ℕ → ℝ) (N q a₀ t₀ a : ℕ) : Finset PolicyDescriptor :=
  (policyDescriptorList A N q a₀ t₀).filter fun b => a < descriptorAnchor b

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularStateData
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff

structure AngularStateData where
  Q : DyadicSquare
  ρ : Measure Plane
  mass : ℝ → ℝ
  N : ℕ
  q : ℕ
  a₀ : ℕ
  t₀ : ℕ
  a : ℕ
  v : ℕ
  J : ℕ
  i : ℕ
  lam : ℝ
  sig : ℝ
  X : CellPath
  Y : CellPath

namespace AngularStateData

noncomputable def profile (d : AngularStateData) (n : ℕ) : ℝ := d.mass n-(n:ℝ)/d.N

noncomputable def retainedList (d : AngularStateData) (p : ℕ) : Finset PolicyDescriptor :=
  remainingPolicyDescriptors d.profile d.N d.q d.a₀ d.t₀ p

noncomputable def cellEnergy (d : AngularStateData) (S : Finset PolicyDescriptor)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ)
    (p : ℕ) (Ψ : ℝ → ℝ) (row : CellPath × CellPath) : ℝ≥0∞ :=
  sourceAngularH p d.v Ψ
    (fun z => sourceAngularTransform d.ρ (d.Q.descendant row.1).carrier
      (((2:ℝ)^d.N)^(-d.mass p))
      (inheritedCircleSymbol S id (k 0) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (h 0)) z.1 z.2)
    (fun z => sourceAngularTransform d.ρ (d.Q.descendant row.2).carrier
      (((2:ℝ)^d.N)^(-d.mass p))
      (inheritedCircleSymbol S id (k 1) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (h 1)) z.1 z.2)

noncomputable def energy (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (Ψ : ℝ → ℝ) : ℝ≥0∞ :=
  d.cellEnergy (d.retainedList d.a) k h d.a Ψ (d.X,d.Y)

noncomputable def childEnergy (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ)
    (p : ℕ) (Ψ : ℝ → ℝ) : CellPath × CellPath → ℝ≥0∞ :=
  d.cellEnergy (d.retainedList p) k h p Ψ

noncomputable def children (d : AngularStateData) (p : ℕ) : Finset (CellPath × CellPath) :=
  sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a)

noncomputable def childMaximum (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ)
    (p : ℕ) (Ψ : ℝ → ℝ) : ℝ :=
  finiteEnergyMaximum (d.children p) (d.childEnergy k h p Ψ)

end AngularStateData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularStateSuccessor
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace AngularStateData

def successor (d : AngularStateData) (p : ℕ) (row : CellPath × CellPath) : AngularStateData :=
  {d with a := p, X := row.1, Y := row.2}

end AngularStateData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualFarBuffer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def sourceFarBuffer (N L : ℕ) (sig : ℝ) : ℕ :=
  max L ⌈10*sig*(N:ℝ)⌉₊

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualComparableFarError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def angularComparableFarContribution (Q₁ Q₂ : DyadicSquare)
    (ρ ν : Measure Plane) (A B : CellPath) (a d : ℕ) (v Ma₁ Ma₂ : ℝ)
    (F : (Fin 4 → Plane) → ℂ) : ℂ :=
  (((2:ℝ)^(2*(v-a)))/(Ma₁^2*Ma₂^2)) •
    ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
        if ¬ angularNear Q₁ Q₂ (a+d) row col then
          ∫ x in angularLengthComparable, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
        else 0

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualNoncomparableFar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff
attribute [local instance] Classical.propDecidable

noncomputable def angularNoncomparableFarContribution (Q₁ Q₂ : DyadicSquare)
    (ρ ν : Measure Plane) (A B : CellPath) (a d : ℕ) (v Ma₁ Ma₂ : ℝ)
    (F : (Fin 4 → Plane) → ℂ) : ℂ :=
  (((2:ℝ)^(2*(v-a)))/(Ma₁^2*Ma₂^2)) •
    ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
        if ¬ angularNear Q₁ Q₂ (a+d) row col then
          ∫ x in (angularLengthLeft ∪ angularLengthRight), F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
        else 0

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceGoodSet
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

@[fun_prop] theorem measurable_pairRadialUnit :
    Measurable (fun z : Plane × Plane => sourceRadialUnit z.2 z.1) := by
  apply Measurable.subtype_mk
  change Measurable (fun z : Plane × Plane => sourceRadialVector z.2 z.1)
  unfold sourceRadialVector
  exact Measurable.ite (isClosed_eq continuous_fst continuous_snd).measurableSet
    measurable_const (by fun_prop)

noncomputable def endpointDescriptorGood (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (d : PolicyDescriptor) : Set (Plane × UnitCircle) :=
  {z | ∀ P ∈ dyadicPaths (descriptorAnchor d),
    z.1 ∈ (Q.descendant P).carrier →
    z.2 ∈ descriptorGoodSet Q ρ m N lam sig J i P d}

noncomputable def positiveDistanceGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N q a t : ℕ) (lam sig : ℝ) (J i : ℕ) : Set (Plane × Plane) :=
  {z | ∀ d ∈ policyDescriptorList (fun n => m n-(n:ℝ)/(N:ℝ)) N q a t,
    (z.1, sourceRadialUnit z.2 z.1) ∈ endpointDescriptorGood Q ρ m N lam sig J i d ∧
    (z.2, sourceRadialUnit z.2 z.1) ∈ endpointDescriptorGood Q ρ m N lam sig J i d}

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistancePushforward
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

structure PositiveDistanceData where
  Q : DyadicSquare
  ρ : Measure Plane
  mass : ℝ → ℝ
  N : ℕ
  q : ℕ
  a : ℕ
  t : ℕ
  lam : ℝ
  sig : ℝ
  J : ℕ
  i : ℕ
  X : CellPath
  Y : CellPath

namespace PositiveDistanceData

noncomputable def good (d : PositiveDistanceData) : Set (Plane × Plane) :=
  positiveDistanceGoodSet d.Q d.ρ d.mass d.N d.q d.a d.t d.lam d.sig d.J d.i

noncomputable def cellPair (d : PositiveDistanceData) : Measure (Plane × Plane) :=
  (d.ρ.restrict (d.Q.descendant d.X).carrier).prod
    (d.ρ.restrict (d.Q.descendant d.Y).carrier)

noncomputable def pair (d : PositiveDistanceData) : Measure (Plane × Plane) :=
  d.cellPair.restrict d.good

noncomputable def distance (d : PositiveDistanceData) : Measure ℝ :=
  Measure.map (fun z : Plane × Plane => dist z.1 z.2) d.pair

instance cellPair_finite (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    IsFiniteMeasure d.cellPair := by unfold cellPair; infer_instance

instance pair_finite (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    IsFiniteMeasure d.pair := by unfold pair; infer_instance

instance distance_finite (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    IsFiniteMeasure d.distance := by unfold distance; infer_instance

noncomputable def width (d : PositiveDistanceData) : ℝ := (2:ℝ)^(-(d.t:ℝ))

noncomputable def levelMass (d : PositiveDistanceData) : ℝ :=
  ((2:ℝ)^d.N)^(-d.mass d.a)

noncomputable def normalization (d : PositiveDistanceData) : ℝ≥0∞ :=
  ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a) / d.levelMass^4)

noncomputable def coincidence (d : PositiveDistanceData) : ℝ≥0∞ :=
  d.normalization * (d.pair.prod d.pair)
    {z | |dist z.1.1 z.1.2 - dist z.2.1 z.2.2| ≤ 100*d.width}

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_Bins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set

def realBin (w : ℝ) (j : ℤ) : Set ℝ :=
  Set.Ico ((j : ℝ)*w) (((j+1 : ℤ) : ℝ)*w)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_BinOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

noncomputable def binL2Norm (μ : Measure ℝ) (w : ℝ) : ℝ≥0∞ :=
  (∑' j : ℤ, (μ (realBin w j))^2)^(1/2 : ℝ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_BinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

noncomputable def binKernelWeight (h : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (4/((h:ℝ)+1/2)^2)

noncomputable def binKernelConstant : ℝ≥0∞ := ∑' h : ℤ, binKernelWeight h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_BinBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

noncomputable def bandOffsets (C : ℝ) : Finset ℤ := Finset.Icc (-(⌈C⌉₊ : ℤ)-2) ((⌈C⌉₊ : ℤ)+2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceOriginalSpatial
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

noncomputable def fourCells (d e : PositiveDistanceData) : Fin 4 → Measure Plane :=
  ![d.ρ.restrict (d.Q.descendant d.X).carrier,d.ρ.restrict (d.Q.descendant d.Y).carrier,
    e.ρ.restrict (e.Q.descendant e.X).carrier,e.ρ.restrict (e.Q.descendant e.Y).carrier]

instance fourCells_finite (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] (i : Fin 4) :
    IsFiniteMeasure (fourCells d e i) := by
  fin_cases i <;> dsimp [fourCells] <;> infer_instance

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ComparablePositiveRebin
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

def angularSeparated (Q₁ Q₂ : DyadicSquare) (b : ℕ)
    (row col : CellPath × CellPath) : Prop :=
  (100*(2:ℝ)^(-(b:ℝ)) ≤ dist (Q₁.descendant row.1).center (Q₁.descendant col.1).center ∧
    dist (Q₁.descendant row.1).center (Q₁.descendant col.1).center ≤ 2000*(2:ℝ)^(-(b:ℝ))) ∧
  (100*(2:ℝ)^(-(b:ℝ)) ≤ dist (Q₂.descendant row.2).center (Q₂.descendant col.2).center ∧
    dist (Q₂.descendant row.2).center (Q₂.descendant col.2).center ≤ 2000*(2:ℝ)^(-(b:ℝ)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceRebinBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace PositiveDistanceData

abbrev atCells (d : PositiveDistanceData) (X Y : CellPath) : PositiveDistanceData :=
  {d with X := X, Y := Y}

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_SeparatedDistanceMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

namespace PositiveDistanceData

noncomputable def separatedMaximum (d e : PositiveDistanceData)
    (C : Finset (CellPath × CellPath)) (b : ℕ) : ℝ≥0∞ :=
  ((C ×ˢ C).filter (fun z => angularSeparated d.Q e.Q b z.1 z.2)).sup
    (fun z => max (d.atCells z.1.1 z.2.1).coincidence (e.atCells z.1.2 z.2.2).coincidence)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularStateContributions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace AngularStateData

noncomputable def contribution (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (p : ℕ) (Ψ : ℝ → ℝ)
    (rel : (CellPath × CellPath) → (CellPath × CellPath) → Prop) : ℂ :=
  angularCellContribution d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a) d.a d.v Ψ
    (((2:ℝ)^d.N)^(-d.mass d.a)) (((2:ℝ)^d.N)^(-d.mass d.a))
    (((2:ℝ)^d.N)^(-d.mass p)) (((2:ℝ)^d.N)^(-d.mass p))
    (inheritedCircleSymbol (d.retainedList d.a) id (k 0) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (h 0))
    (inheritedCircleSymbol (d.retainedList d.a) id (k 1) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (h 1)) rel

noncomputable def nearContribution (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (p : ℕ) (Ψ : ℝ → ℝ) : ℂ :=
  d.contribution k h p Ψ (angularNear d.Q d.Q p)

noncomputable def farContribution (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (p : ℕ) (Ψ : ℝ → ℝ) : ℂ :=
  d.contribution k h p Ψ (fun row col => ¬ angularNear d.Q d.Q p row col)

def distanceSuccessor (d : AngularStateData) (b : ℕ) : PositiveDistanceData :=
  ⟨d.Q,d.ρ,d.mass,d.N,d.q,b,d.v,d.lam,d.sig,d.J,d.i+1,[],[]⟩

noncomputable def farDistanceMaximum (d : AngularStateData) (b : ℕ) : ℝ≥0∞ :=
  (d.distanceSuccessor b).separatedMaximum (d.distanceSuccessor b) (d.children b) b

noncomputable def farSum (d : AngularStateData) (p : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc (d.a+9) (p+5),
    ((2:ℝ)^d.N)^(-2*(d.profile b-d.profile d.a)+4000*(d.lam+d.sig)) *
      (d.farDistanceMaximum b).toReal

end AngularStateData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ParentBinFamily
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

abbrev ParentDistanceBinLabel := Σ _ : CellPath × CellPath, ℕ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RotatedGraphEligibility
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

def RotatedAngularLabelEligible (ρ : Measure Plane) (X : Set Plane)
    (b : Plane → UnitCircle → ℂ) (n j : ℕ) (axis : ℝ) : Prop :=
  AngularLabelEligible ρ X (fun x u => b x (sourceCircleRotate axis u)) n j

def SourceParentBinEligible (N : ℕ) (sig t : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (b₁ b₂ : Plane → UnitCircle → ℂ) (e : ParentDistanceBinLabel) : Prop :=
  RotatedAngularLabelEligible ρ (X.descendant e.1.1).carrier b₁
    (angularBinCount (graphUncappedAngularScale N sig t)) e.2 (sourceParentAxis X Y) ∧
  RotatedAngularLabelEligible ν (Y.descendant e.1.2).carrier b₂
    (angularBinCount (graphUncappedAngularScale N sig t)) e.2 (sourceParentAxis X Y)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualClassFamilies
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

structure ActualClassFamily (Q : DyadicSquare) (μ : Measure Plane) (N H : ℕ)
    (δ lam sig : ℝ) (m : List ℕ → ℝ → ℝ) : Prop where
  count : (retainedClassLabels Q μ N (N/H) (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))).card ≤ (4*N+1)^(2*H+1)
  discarded : μ (retainedClassUnion Q μ N (N/H) (ENNReal.ofReal (((2:ℝ)^N)^(-lam))))ᶜ ≤
    ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
      (((4*N+1)^(2*H+1):ℕ):ENNReal)*ENNReal.ofReal (((2:ℝ)^N)^(-lam))
  mass : ∀ T ∈ retainedClassLabels Q μ N (N/H) (ENNReal.ofReal (((2:ℝ)^N)^(-lam))),
    ENNReal.ofReal (((2:ℝ)^N)^(-lam)) ≤
      classMeasure Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N (N/H)) T univ
  profiles : ∀ T ∈ retainedClassLabels Q μ N (N/H) (ENNReal.ofReal (((2:ℝ)^N)^(-lam))),
    RegularizedProfileData Q
      (normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N (N/H)) T)
        N (N/H) δ lam (m T) ∧
    SourceAngularBounds Q
      (normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N (N/H)) T)
        (m T) N lam sig

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualOuterMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

noncomputable def sourceSmoothingLevels (sig kap : ℝ) : ℕ :=
  Nat.ceil (100*(1/sig+1/kap)+100)

noncomputable def sourcePolicyBlock (N : ℕ) (kap : ℝ) : ℕ := Nat.ceil (kap*(N:ℝ))

noncomputable def outerDescriptorList (m : ℝ → ℝ) (N q c : ℕ) : Finset PolicyDescriptor :=
  insert (.parallel 0 c) (policyDescriptorList (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) N q c N)

noncomputable def outerEndpointMask (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig kap : ℝ) (c : ℕ) : Plane → UnitCircle → ℝ :=
  descriptorListMask Q ρ m N lam sig (sourceSmoothingLevels sig kap) 0
    (outerDescriptorList m N (sourcePolicyBlock N kap) c)

@[fun_prop] theorem measurable_outerEndpointMask (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig kap : ℝ) (c : ℕ) :
    Measurable (fun z : Plane × UnitCircle => outerEndpointMask Q ρ m N lam sig kap c z.1 z.2) :=
  measurable_descriptorListMask _ _ _ _ _ _ _ _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_RetainedPairMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def actualClassDomain (Q : DyadicSquare) (μ : Measure Plane) (N B : ℕ) (T : List ℕ) : Set Plane :=
  leafUnion Q (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T)

noncomputable def actualClassMeasure (Q : DyadicSquare) (μ : Measure Plane) (N B : ℕ) (T : List ℕ) : Measure Plane :=
  normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T

theorem actualClassDomain_disjoint (Q : DyadicSquare) (hQ : 0 < Q.side) (μ : Measure Plane)
    (N B : ℕ) {T U : List ℕ} (hTU : T ≠ U) :
    Disjoint (actualClassDomain Q μ N B T) (actualClassDomain Q μ N B U) := by
  apply leafUnion_disjoint Q hQ (N := N)
  · intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  · exact classLeaves_disjoint _ _ hTU

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualClassMass
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable def actualClassMass (Q : DyadicSquare) (μ : Measure Plane) (N B : ℕ) (T : List ℕ) : ℝ≥0 :=
  (μ (actualClassDomain Q μ N B T)).toNNReal

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceEligibleIndices
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def distanceSlotBin (j k : ℕ) (l : Fin 4) : ℕ := ![j,j,k,k] l

def GraphDistanceIndexEligible (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (β γ : Plane → UnitCircle → ℂ) (m : ℕ) (axis : ℝ) (e : GraphNonedgeIndex) : Prop :=
  ∀ l : Fin 4, RotatedAngularLabelEligible (![ρ,ν,ν,ρ] l)
    (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] e.1 l).carrier (![β,γ,γ,β] l)
    m (distanceSlotBin e.2.1.1 e.2.1.2 l) axis

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceMatrixData
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def distanceMatrixIndex (row col : CellPath × CellPath) (j b : ℕ) (plus : Bool) : GraphNonedgeIndex :=
  (((row.1,col.1),(row.2,col.2)),((j,b),plus))

noncomputable def distanceMatrixNeighbors (I : Finset GraphNonedgeIndex) (p j b : ℕ)
    (plus reverse : Bool) (row : CellPath × CellPath) : Finset (CellPath × CellPath) := by
  classical
  exact ((dyadicPaths p) ×ˢ (dyadicPaths p)).filter (fun col =>
    (if reverse then distanceMatrixIndex col row j b plus else distanceMatrixIndex row col j b plus) ∈ I)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_InverseLeibniz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

noncomputable def inverseLeibnizTerms {ι : Type*} [DecidableEq ι] (j : ℕ) (S : Finset ι) :
    List (ℂ × (ι → ℕ)) :=
  (inverseStationaryExpr j).terms.flatMap (fun a =>
    (orderedDerivAssignments S a.2).map (fun k => (a.1,k)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

namespace PositiveDistanceData

noncomputable def minimalMask (d : PositiveDistanceData) (z : Plane × Plane) : ℝ :=
  descriptorListMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i
    (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)
    z.1 (sourceRadialUnit z.2 z.1) *
  descriptorListMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i
    (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)
    z.2 (sourceRadialUnit z.2 z.1)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceWeight
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

noncomputable def spatialWeight (d : PositiveDistanceData) (z : Plane × Plane) : ℝ :=
  (dist z.1 z.2 / (2:ℝ)^(-(d.a:ℝ)))^(-(1/2:ℝ)) * d.minimalMask z

def StronglySeparated (d : PositiveDistanceData) : Prop :=
  (d.Q.descendant d.X).side ≤ (2:ℝ)^(-(d.a:ℝ)) ∧
  (d.Q.descendant d.Y).side ≤ (2:ℝ)^(-(d.a:ℝ)) ∧
  100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ∧
  dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ))

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_WeightedDistancePushforward
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

noncomputable def weightedPair (d : PositiveDistanceData) : Measure (Plane × Plane) :=
  d.cellPair.withDensity (fun z => ENNReal.ofReal (d.levelMass^(-2:ℤ) * d.spatialWeight z))

noncomputable def weightedDistance (d : PositiveDistanceData) : Measure ℝ :=
  Measure.map (fun z : Plane × Plane => dist z.1 z.2) d.weightedPair

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_MinimalPairSymbol
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

namespace PositiveDistanceData

noncomputable def pairMaskSymbol (d : PositiveDistanceData) (z : Plane × Plane)
    (dir : UnitCircle) : ℂ :=
  (descriptorListMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i
    (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t) z.1 dir : ℂ) *
  (descriptorListMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i
    (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t) z.2 dir : ℂ)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RootEndpointData
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

structure RootEndpointData where
  Q : DyadicSquare
  ρ : Measure Plane
  mass : ℝ → ℝ
  lam : ℝ
  J : ℕ
  i : ℕ
  S : Finset PolicyDescriptor

namespace RootEndpointData

noncomputable def mask (d : RootEndpointData) (N : ℕ) (sig : ℝ) : Plane → UnitCircle → ℝ :=
  descriptorListMask d.Q d.ρ d.mass N d.lam sig d.J d.i d.S

noncomputable def symbol (d : RootEndpointData) (N : ℕ) (sig : ℝ)
    (k : PolicyDescriptor → ℕ) (h : Plane → ℂ) : Plane → UnitCircle → ℂ :=
  inheritedCircleSymbol d.S id k d.Q d.ρ d.mass N d.lam sig d.J d.i h

noncomputable def ofOuter (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig kap : ℝ) (c : ℕ) : RootEndpointData :=
  ⟨Q,ρ,m,lam,sourceSmoothingLevels sig kap,0,
    outerDescriptorList m N (sourcePolicyBlock N kap) c⟩

end RootEndpointData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_RootPairSymbols
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def rootPairMask (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) : ℝ :=
  d.mask N sig z.1 (sourceRadialUnit z.2 z.1) *
    e.mask N sig z.2 (sourceRadialUnit z.2 z.1)

noncomputable def rootSpatialWeight (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) : ℝ :=
  (dist z.1 z.2)^(-(1/2:ℝ)) * rootPairMask d e N sig z

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootWeightedDistance
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal

noncomputable def rootWeightedPair (d e : RootEndpointData) (N : ℕ) (sig : ℝ) :
    Measure (Plane × Plane) :=
  (d.ρ.prod e.ρ).withDensity (fun z => ENNReal.ofReal (rootSpatialWeight d e N sig z))

noncomputable def rootWeightedDistance (d e : RootEndpointData) (N : ℕ) (sig : ℝ) : Measure ℝ :=
  Measure.map (fun z : Plane × Plane => dist z.1 z.2) (rootWeightedPair d e N sig)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellLeibnizSymbols
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

abbrev PairMaskIndex := PolicyDescriptor × Fin 2

noncomputable def pairMaskIndices (S : Finset PolicyDescriptor) : Finset PairMaskIndex :=
  S.product Finset.univ

noncomputable def assignmentScale (S : Finset PolicyDescriptor) (N : ℕ) (sig : ℝ)
    (k : PairMaskIndex → ℕ) : ℝ :=
  ∏ a ∈ pairMaskIndices S, (sourceAngularRadius N sig (descriptorLength a.1))⁻¹^(k a)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellEndpointTerms
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ComplexConjugate
namespace PositiveDistanceData

noncomputable def inverseDescriptorList (d : PositiveDistanceData) : Finset PolicyDescriptor :=
  policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t

noncomputable def inverseEndpointSymbol (d : PositiveDistanceData) (k : PairMaskIndex → ℕ)
    (l : Fin 2) : Plane → UnitCircle → ℂ :=
  inheritedCircleSymbol d.inverseDescriptorList id (fun b => k (b,l)) d.Q d.ρ d.mass
    d.N d.lam d.sig d.J d.i (fun _ => 1)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootLeibniz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

abbrev RootMaskIndex := PolicyDescriptor ⊕ PolicyDescriptor

noncomputable def rootMaskIndices (d e : RootEndpointData) : Finset RootMaskIndex := d.S.disjSum e.S

def rootMaskDescriptor : RootMaskIndex → PolicyDescriptor := Sum.elim id id

noncomputable def rootAssignmentScale (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (k : RootMaskIndex → ℕ) : ℝ :=
  ∏ b ∈ rootMaskIndices d e, (sourceAngularRadius N sig (descriptorLength (rootMaskDescriptor b)))⁻¹^(k b)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RootEndpointTerms
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def rootLeftSymbol (d : RootEndpointData) (N : ℕ) (sig : ℝ)
    (k : RootMaskIndex → ℕ) : Plane → UnitCircle → ℂ :=
  d.symbol N sig (fun b => k (.inl b)) (fun _ => 1)

noncomputable def rootRightSymbol (e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (k : RootMaskIndex → ℕ) : Plane → UnitCircle → ℂ :=
  e.symbol N sig (fun b => k (.inr b)) (fun _ => 1)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_RootNormalizedKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

noncomputable def rootAbsorbedCoefficient (d e : RootEndpointData) (N : ℕ) (sig : ℝ) (j : ℕ) (b : ℂ × (RootMaskIndex → ℕ)) : ℂ :=
  b.1 * ((2:ℝ)^(-(j:ℝ)*((N:ℝ)-0))*rootAssignmentScale d e N sig b.2 : ℝ)

noncomputable def rootNormalizedKernel (d e : RootEndpointData) (N : ℕ) (sig : ℝ) (n : ℕ)
    (r : ℝ) (ψ : UnitCircle → ℂ) (z : Plane × Plane) : ℂ :=
  (((r*(2:ℝ)^(-(0:ℝ)))^(1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
    ((((r/(2:ℝ)^(N:ℝ))⁻¹)^j:ℝ):ℂ) *
      ((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun b =>
        rootAbsorbedCoefficient d e N sig j b *
          (((((dist z.1 z.2/(2:ℝ)^(-(0:ℝ)))⁻¹)^j:ℝ):ℂ) *
            sourceDistanceKernel ψ (rootLeftSymbol d N sig b.2)
              (rootRightSymbol e N sig b.2) r z.1 z.2))).sum

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_NormalizedHighShellKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
namespace PositiveDistanceData

noncomputable def absorbedInverseCoefficient (d : PositiveDistanceData) (j : ℕ)
    (v : ℝ) (b : ℂ × (PairMaskIndex → ℕ)) : ℂ :=
  b.1 * ((2:ℝ)^(-(j:ℝ)*(v-d.a))*assignmentScale d.inverseDescriptorList d.N d.sig b.2 : ℝ)

noncomputable def normalizedHighShellKernel (d : PositiveDistanceData) (n : ℕ)
    (v r : ℝ) (ψ : UnitCircle → ℂ) (z : Plane × Plane) : ℂ :=
  (((r*(2:ℝ)^(-(d.a:ℝ)))^(1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
    ((((r/(2:ℝ)^v)⁻¹)^j:ℝ):ℂ) *
      ((inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)).map (fun b =>
        d.absorbedInverseCoefficient j v b *
          (((((dist z.1 z.2/(2:ℝ)^(-(d.a:ℝ)))⁻¹)^j:ℝ):ℂ) *
            sourceDistanceKernel ψ (d.inverseEndpointSymbol b.2 0)
              (d.inverseEndpointSymbol b.2 1) r z.1 z.2))).sum

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_RootFourierError
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

noncomputable def rootNormalizedF (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (n : ℕ) (U V : DyadicSquare) (r : ℝ) : ℂ :=
  ∫ z, rootNormalizedKernel d e N sig n r (sourceConeCircle (sourceParentAxis U V)) z ∂d.ρ.prod e.ρ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ParentHFBridge
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def sourceParentHF (a v : ℝ) (Ψ : ℝ → ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) : ℝ≥0∞ :=
  sourceDistanceHF a v Ψ (sourceConeCircle (sourceParentAxis X Y))
    (fun z => sourceAngularTransform ρ X.carrier M₁ b₁ z.1 z.2)
    (fun z => sourceAngularTransform ν Y.carrier M₂ b₂ z.1 z.2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SpatialAnnulusKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric Filter
open scoped ContDiff Topology SchwartzMap

noncomputable def spatialInnerBump (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : Plane) :=
  ⟨δ/2, δ, half_pos hδ, half_lt_self hδ⟩

noncomputable def spatialOuterBump (L : ℝ) (hL : 0 < L) : ContDiffBump (0 : Plane) :=
  ⟨L, L+1, hL, by linarith⟩

noncomputable def spatialAnnulusKernel (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (z : Plane) : ℂ :=
  ↑(spatialOuterBump L hL z * (1-spatialInnerBump δ hδ z) * (‖z‖^j)⁻¹)

theorem spatialAnnulusKernel_smooth (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : ContDiff ℝ ∞ (spatialAnnulusKernel δ L hδ hL j) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have he : spatialAnnulusKernel δ L hδ hL j =ᶠ[𝓝 0] (fun _ => 0) := by
      filter_upwards [(spatialInnerBump δ hδ).eventuallyEq_one] with z hz
      simp [spatialAnnulusKernel, hz]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hn : ContDiffAt ℝ ∞ (fun z : Plane => (‖z‖^j)⁻¹) z :=
      ((contDiffAt_norm ℝ hz).pow j).inv (pow_ne_zero _ (norm_ne_zero_iff.mpr hz))
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (((spatialOuterBump L hL).contDiffAt.mul
        (contDiffAt_const.sub (spatialInnerBump δ hδ).contDiffAt)).mul hn)

theorem spatialAnnulusKernel_compact (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : HasCompactSupport (spatialAnnulusKernel δ L hδ hL j) := by
  exact (((spatialOuterBump L hL).hasCompactSupport.mul_right).mul_right).comp_left
    (map_zero Complex.ofRealCLM)

noncomputable def spatialAnnulusSchwartz (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : 𝓢(Plane, ℂ) :=
  (spatialAnnulusKernel_compact δ L hδ hL j).toSchwartzMap
    (spatialAnnulusKernel_smooth δ L hδ hL j)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SpatialFourierSeparation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

noncomputable def spatialFourierCoeff (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : 𝓢(Plane, ℂ) := 𝓕 (spatialAnnulusSchwartz δ L hδ hL j)

noncomputable def spatialFourierCost (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : ℝ := ∫ ξ, ‖spatialFourierCoeff δ L hδ hL j ξ‖

noncomputable def spatialFourierPhase (s : ℝ) (ξ x : Plane) : ℂ :=
  Complex.exp (↑(2*Real.pi*inner ℝ ξ (s⁻¹ • x))*Complex.I)

@[fun_prop] theorem spatialFourierPhase_continuous (s : ℝ) :
    Continuous (fun z : Plane × Plane => spatialFourierPhase s z.1 z.2) := by
  unfold spatialFourierPhase
  fun_prop

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SpatialFourierIntegration
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter
open scoped ComplexConjugate

noncomputable def spatialPairPhase (s : ℝ) (ξ : Plane) (z : Plane × Plane) : ℂ :=
  spatialFourierPhase s ξ z.1 * conj (spatialFourierPhase s ξ z.2)

@[fun_prop] theorem spatialPairPhase_continuous (s : ℝ) :
    Continuous (fun p : Plane × (Plane × Plane) => spatialPairPhase s p.1 p.2) := by
  unfold spatialPairPhase spatialFourierPhase
  fun_prop

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SpatialPhasedSymbols
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ComplexConjugate

noncomputable def spatialPhasedSymbol (s : ℝ) (ξ : Plane)
    (b : Plane → UnitCircle → ℂ) (x : Plane) (ω : UnitCircle) : ℂ :=
  spatialFourierPhase s ξ x * b x ω

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_RootNormalizedCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def rootSpatialLeibnizCost (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (d e : RootEndpointData) (j : ℕ) : ℝ :=
  spatialFourierCost δ L hδ hL j *
    (((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun b => ‖b.1‖)).sum * (2:ℝ)^j)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RootShellData
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

structure RootShellData where
  left : RootEndpointData
  right : RootEndpointData
  N : ℕ
  sig : ℝ
  U : DyadicSquare
  V : DyadicSquare

namespace RootShellData

noncomputable def indices (d : RootShellData) := rootMaskIndices d.left d.right
noncomputable def endpointLeft (d : RootShellData) (k : RootMaskIndex → ℕ) := rootLeftSymbol d.left d.N d.sig k
noncomputable def endpointRight (d : RootShellData) (k : RootMaskIndex → ℕ) := rootRightSymbol d.right d.N d.sig k
noncomputable def coefficient (d : RootShellData) (j : ℕ) (b : ℂ × (RootMaskIndex → ℕ)) :=
  rootAbsorbedCoefficient d.left d.right d.N d.sig j b
noncomputable def mainF (d : RootShellData) (n : ℕ) := rootNormalizedF d.left d.right d.N d.sig n d.U d.V
noncomputable def measure (d : RootShellData) := rootWeightedDistance d.left d.right d.N d.sig
noncomputable def cost (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ) :=
  rootSpatialLeibnizCost δ L hδ hL d.left d.right j

end RootShellData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RootShellMixture
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace RootShellData

noncomputable def inversePhasedForm (d : RootShellData)
    (k : RootMaskIndex → ℕ) (ξ : Plane) : ℝ → ℂ :=
  sourceParentDistanceF d.U d.V
    d.left.ρ d.right.ρ 1 1
    (spatialPhasedSymbol 1 ξ (d.endpointLeft k))
    (spatialPhasedSymbol 1 ξ (d.endpointRight k))

noncomputable def inverseSpatialMixture (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ)
    (k : RootMaskIndex → ℕ) (r : ℝ) : ℂ :=
  ∫ ξ, spatialFourierCoeff δ L hδ hL j ξ * d.inversePhasedForm k ξ r

noncomputable def inversePhasedBound (d : RootShellData) (j : ℕ) : ℝ :=
  (1*(symbolDerivativeConstant (2*j)^(2*j))*(symbolDerivativeConstant (2*j)^(2*j))*
    sourceArcLength.real univ) * ((d.left.ρ d.U.carrier).toReal/1)*
    ((d.right.ρ d.V.carrier).toReal/1)

end RootShellData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RootShellOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace RootShellData

noncomputable def inverseOrderForm (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ) (r : ℝ) : ℂ :=
  ((inverseLeibnizTerms j (d.indices)).map (fun b =>
    d.coefficient j b*d.inverseSpatialMixture δ L hδ hL j b.2 r)).sum

end RootShellData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_RootParentEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace RootShellData

noncomputable def inversePhasedHF (d : RootShellData) (v : ℝ) (Ψ : ℝ → ℝ)
    (k : RootMaskIndex → ℕ) (ξ : Plane) : ℝ≥0∞ :=
  sourceParentHF (0:ℝ) v Ψ d.U d.V
    d.left.ρ d.right.ρ 1 1
    (spatialPhasedSymbol 1 ξ (d.endpointLeft k))
    (spatialPhasedSymbol 1 ξ (d.endpointRight k))

end RootShellData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootSupremum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace RootShellData

noncomputable def inverseShellEnergies (d : RootShellData) (n : ℕ)
    (v : ℝ) (Ψ : ℝ → ℝ) : Set ℝ :=
  insert 0 {h | ∃ j ∈ Finset.range (n+1),
    ∃ b ∈ inverseLeibnizTerms j (d.indices),
    ∃ ξ, h = (d.inversePhasedHF v Ψ b.2 ξ).toReal}

noncomputable def inverseShellSupremum (d : RootShellData) (n : ℕ)
    (v : ℝ) (Ψ : ℝ → ℝ) : ℝ := sSup (d.inverseShellEnergies n v Ψ)

end RootShellData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_OuterRootEquation21
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

namespace RootShellData

noncomputable def ofOuter (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam₁ lam₂ sig kap : ℝ) (c : ℕ) (U V : DyadicSquare) : RootShellData :=
  ⟨RootEndpointData.ofOuter Q₁ ρ m₁ N lam₁ sig kap c,
    RootEndpointData.ofOuter Q₂ ν m₂ N lam₂ sig kap c,N,sig,U,V⟩

end RootShellData

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

noncomputable def dyadicShell (N : ℕ) : Set ℝ :=
  {r | (2 : ℝ)^((N : ℝ)-1) ≤ |r| ∧ |r| ≤ (2 : ℝ)^((N : ℝ)+1)}

noncomputable def shellEnergy (μ : Measure ℝ) (N : ℕ) : ℝ :=
  ∫ r in dyadicShell N, ‖charFun μ r‖^2

noncomputable def variationDistance (τ σ : FiniteMeasure ℝ) : ℝ≥0∞ :=
  ((τ : Measure ℝ).toSignedMeasure-(σ : Measure ℝ).toSignedMeasure).totalVariation univ

def HasShellApproximations (τ : FiniteMeasure ℝ) : Prop :=
  ∃ τN : ℕ → FiniteMeasure ℝ, ∃ η γ Ctv Cshell : ℝ,
    0 < η ∧ 0 < γ ∧ 0 < Ctv ∧ 0 < Cshell ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      variationDistance τ (τN N) ≤ ENNReal.ofReal (Ctv*(2 : ℝ)^(-η*(N : ℝ))) ∧
      shellEnergy (τN N) N ≤ Cshell*(2 : ℝ)^(-γ*(N : ℝ))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SourceAssemblyParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff

noncomputable def assemblyShellBump : ContDiffBump (5/4 : ℝ) where
  rIn := 3/4
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_RootSimilarityGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

noncomputable def DyadicSquare.dilate (Q : DyadicSquare) (s : ℝ) : DyadicSquare :=
  ⟨s*Q.x,s*Q.y,s*Q.side⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ActualDistanceDegrees
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def activeDistanceMatrixNeighbors (I : Finset GraphNonedgeIndex)
    (p j b : ℕ) (θ axis : ℝ) (plus reverse : Bool) (row : CellPath × CellPath) :
    Finset (CellPath × CellPath) := by
  classical
  exact if (tsupport (graphSourceWeight true plus axis (angularBinCount θ) j b)).Nonempty
    then distanceMatrixNeighbors I p j b plus reverse row else ∅

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_PrefixSuccessorEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

noncomputable def policyCellEnergy (d : PositiveDistanceData)
    (S : Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ)
    (h : Fin 2 → Plane → ℂ) (p : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    (row : CellPath × CellPath) : ℝ≥0∞ :=
  sourceAngularH p v Ψ
    (fun z => sourceAngularTransform d.ρ (d.Q.descendant row.1).carrier
      (((2:ℝ)^d.N)^(-d.mass p))
      (inheritedCircleSymbol S id (k 0) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (h 0)) z.1 z.2)
    (fun z => sourceAngularTransform d.ρ (d.Q.descendant row.2).carrier
      (((2:ℝ)^d.N)^(-d.mass p))
      (inheritedCircleSymbol S id (k 1) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (h 1)) z.1 z.2)

noncomputable def prefixRemainingList (d : PositiveDistanceData) (p : ℕ) : Finset PolicyDescriptor :=
  remainingPolicyDescriptors (fun n => d.mass n-(n:ℝ)/d.N) d.N d.q d.a d.t p

noncomputable def prefixEnergyBound (d : PositiveDistanceData) (K p : ℕ) (W : ℝ) : ℝ :=
  let C := (symbolDerivativeConstant K^K)*d.ρ.real univ/(((2:ℝ)^d.N)^(-d.mass p))
  (2:ℝ)^(2*((d.t:ℝ)-p))*((C^2*sourceArcLength.real univ)*(C^2*sourceArcLength.real univ))*(4*W)

noncomputable def prefixSuccessorEnergies (d : PositiveDistanceData) (K p : ℕ)
    (Ψ : ℝ → ℝ) : Set ℝ :=
  insert 0 {E | ∃ v ∈ Finset.Ioc d.a d.t, (d.t:ℝ)-d.sig*d.N < (v:ℝ) ∧
    ∃ row ∈ sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a),
    ∃ k : Fin 2 → PolicyDescriptor → ℕ,
      (∀ l, ∑ b ∈ d.prefixRemainingList p, k l b ≤ K) ∧
    ∃ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) ∧
      (∀ l x, ‖h l x‖ ≤ 1) ∧
      E = (d.policyCellEnergy (d.prefixRemainingList p) k h p v Ψ row).toReal}

noncomputable def prefixSuccessorSupremum (d : PositiveDistanceData) (K p : ℕ)
    (Ψ : ℝ → ℝ) : ℝ := sSup (d.prefixSuccessorEnergies K p Ψ)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_PrefixGraphSpecialization
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PositiveDistanceData

noncomputable def policyParentEnergy (d : PositiveDistanceData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ)
    (v : ℝ) (Ψ : ℝ → ℝ) : ℝ≥0∞ :=
  sourceParentHF d.a v Ψ (d.Q.descendant d.X) (d.Q.descendant d.Y) d.ρ d.ρ
    d.levelMass d.levelMass
    (inheritedCircleSymbol d.inverseDescriptorList id (k 0) d.Q d.ρ d.mass
      d.N d.lam d.sig d.J d.i (h 0))
    (inheritedCircleSymbol d.inverseDescriptorList id (k 1) d.Q d.ρ d.mass
      d.N d.lam d.sig d.J d.i (h 1))

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellFourierError
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace PositiveDistanceData

noncomputable def normalizedHighShellF (d : PositiveDistanceData) (n : ℕ) (v r : ℝ) : ℂ :=
  (d.levelMass^(-2:ℤ):ℝ) • ∫ z, d.normalizedHighShellKernel n v r
    (sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y))) z ∂d.cellPair

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_DirectPolicyWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

structure DirectPolicyWitness (A : ℕ → ℝ) (N q a₀ t₀ a v : ℕ) (sig : ℝ)
    (d : PolicyDescriptor) : Prop where
  mem : d ∈ remainingPolicyDescriptors A N q a₀ t₀ a
  maximal : descriptorLength d = (remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength
  buffer : sourceFarBuffer N (descriptorLength d) sig = descriptorLength d
  direct_depth : v ≤ a+2*descriptorLength d
  anchor_gt : a < descriptorAnchor d
  anchor_lt : descriptorAnchor d < v
  width : descriptorAnchor d+10*q ≤ v
  companion : PolicyDescriptor.parallel (max a (descriptorAnchor d-descriptorLength d))
    (descriptorAnchor d) ∈ remainingPolicyDescriptors A N q a₀ t₀ a
  g_lt : max a (descriptorAnchor d-descriptorLength d) < descriptorAnchor d
  g_slack : ((max a (descriptorAnchor d-descriptorLength d):ℕ):ℝ)-a ≤ sig*N
  frequency_slack : 10*sig*N ≤ (v:ℝ)-descriptorAnchor d
  depth_scale : ((descriptorAnchor d-a:ℕ):ℝ) ≤ (v:ℝ)-descriptorAnchor d+2*sig*N
  length_scale : (descriptorLength d:ℝ) ≤ (v:ℝ)-descriptorAnchor d+2*sig*N
  midpoint : 2*descriptorAnchor d ≤ a+v+2*q
  shrinks : (remainingPolicyDescriptors A N q a₀ t₀ (descriptorAnchor d)).card <
    (remainingPolicyDescriptors A N q a₀ t₀ a).card
  payment : potential A a v (10*q)+height A a (descriptorAnchor d) ≤
    potential A (descriptorAnchor d) v (10*q)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchTransitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

inductive BranchState where
  | D (a t i : ℕ)
  | H (a₀ t₀ a t i : ℕ)
  deriving DecidableEq

namespace BranchState

def start : BranchState → ℕ
  | .D a _ _ | .H _ _ a _ _ => a
def finish : BranchState → ℕ
  | .D _ t _ | .H _ _ _ t _ => t
def index : BranchState → ℕ
  | .D _ _ i | .H _ _ _ _ i => i
def angular : BranchState → ℕ
  | .D .. => 0
  | .H .. => 1

def Valid (N : ℕ) (sig : ℝ) : BranchState → Prop
  | .D a t _ => a ≤ t ∧ t ≤ N
  | .H a₀ t₀ a t _ => a₀ ≤ a ∧ a ≤ t ∧ t ≤ t₀ ∧ t₀ ≤ N ∧ (t₀:ℝ) ≤ t+sig*N

noncomputable def descriptors (A : ℕ → ℝ) (N q : ℕ) : BranchState → Finset PolicyDescriptor
  | .D a t _ => policyDescriptorList A N q a t
  | .H a₀ t₀ a _ _ => remainingPolicyDescriptors A N q a₀ t₀ a

noncomputable def nearDepth (A : ℕ → ℝ) (N q : ℕ) (sig : ℝ) (s : BranchState) : ℕ :=
  s.finish-2*sourceFarBuffer N ((s.descriptors A N q).sup descriptorLength) sig

end BranchState

inductive BranchLabel where
  | suffix | low | high | near | far | direct
  deriving DecidableEq

inductive BranchStep (A : ℕ → ℝ) (N q : ℕ) (sig : ℝ) :
    BranchState → BranchLabel → BranchState → Prop where
  | suffix {a t i : ℕ} (wide : a+100*q < t)
      (side : a+t < 2*policyDepth A N q a t) :
      BranchStep A N q sig (.D a t i) .suffix (.D a (policyDepth A N q a t) (i+1))
  | low {a t i v : ℕ} (wide : a+100*q < t)
      (mem : v ∈ Finset.Ioc a t) (gap : sig*N ≤ (t:ℝ)-v) :
      BranchStep A N q sig (.D a t i) .low (.D a v (i+1))
  | high {a t i v : ℕ} (wide : a+100*q < t)
      (side : 2*policyDepth A N q a t ≤ a+t)
      (mem : v ∈ Finset.Ioc a t) (gap : (t:ℝ)-v < sig*N) :
      BranchStep A N q sig (.D a t i) .high (.H a t (policyDepth A N q a t) v i)
  | near {a₀ t₀ a t i : ℕ} (wide : a+100*q < t)
      (side : a < (BranchState.H a₀ t₀ a t i).nearDepth A N q sig) :
      BranchStep A N q sig (.H a₀ t₀ a t i) .near
        (.H a₀ t₀ ((BranchState.H a₀ t₀ a t i).nearDepth A N q sig) t i)
  | far {a₀ t₀ a t i b : ℕ} (wide : a+100*q < t)
      (side : a < (BranchState.H a₀ t₀ a t i).nearDepth A N q sig)
      (mem : b ∈ Finset.Icc (a+9) ((BranchState.H a₀ t₀ a t i).nearDepth A N q sig+6)) :
      BranchStep A N q sig (.H a₀ t₀ a t i) .far (.D b t (i+1))
  | direct {a₀ t₀ a t i : ℕ} {e : PolicyDescriptor} (wide : a+100*q < t)
      (witness : DirectPolicyWitness A N q a₀ t₀ a t sig e) :
      BranchStep A N q sig (.H a₀ t₀ a t i) .direct (.H a₀ t₀ (descriptorAnchor e) t i)

def ChargedNear (A : ℕ → ℝ) (N q : ℕ) (s u : BranchState) : Prop :=
  u.start+100*q < u.finish ∧ ∃ e ∈ s.descriptors A N q,
    descriptorLength e = (s.descriptors A N q).sup descriptorLength ∧
    s.start < descriptorAnchor e ∧ descriptorAnchor e ≤ u.start

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

def branchCount (label : ℕ → BranchLabel) (n : ℕ) (kind : BranchLabel) : ℕ :=
  ∑ j ∈ Finset.range n, if label j = kind then 1 else 0

structure PolicyBranch (A : ℕ → ℝ) (N q : ℕ) (sig : ℝ) (n : ℕ) where
  state : ℕ → BranchState
  label : ℕ → BranchLabel
  valid : ∀ j ≤ n, (state j).Valid N sig
  step : ∀ j < n, BranchStep A N q sig (state j) (label j) (state (j+1))

namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

def initialSegment (b : PolicyBranch A N q sig n) (m : ℕ) (hm : m ≤ n) : PolicyBranch A N q sig m :=
  ⟨b.state,b.label,fun j hj => b.valid j (hj.trans hm),fun j hj => b.step j (hj.trans_le hm)⟩

noncomputable def chargedNear (b : PolicyBranch A N q sig n) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun j => b.label j = .near ∧ ChargedNear A N q (b.state j) (b.state (j+1))

noncomputable def charges (b : PolicyBranch A N q sig n) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun j => b.label j = .high ∨ b.label j = .direct ∨
    b.label j = .near ∧ ChargedNear A N q (b.state j) (b.state (j+1))

end PolicyBranch

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def branchCost (A : ℕ → ℝ) (s : BranchState) : BranchLabel → BranchState → ℝ
  | .suffix, u => A u.finish-intervalMin A u.finish s.finish
  | .high, u | .direct, u => height A s.start u.start
  | _, _ => 0

def DiscreteProfileLipschitz (A : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ i ≤ N, ∀ j ≤ N, |A i-A j| ≤ |(i:ℝ)-j|/(N:ℝ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SourceBranchDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

def branchNonlowCount (label : ℕ → BranchLabel) (n : ℕ) : ℕ :=
  branchCount label n .high + branchCount label n .direct + branchCount label n .near +
    branchCount label n .far + branchCount label n .suffix

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchExponentAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def branchExponent (A : ℕ → ℝ) (lam sig eps : ℝ)
    (s : BranchState) (label : BranchLabel) (u : BranchState) : ℝ :=
  -2*(A u.start-A s.start)+branchCost A s label u+
    (if label = .low then 0 else 4000*(lam+sig))+eps

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PrefixLowMaximum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

noncomputable def prefixLowDepths (d : PositiveDistanceData) : Finset ℕ :=
  (Finset.Ioc d.a d.t).filter fun v => (v:ℝ) ≤ (d.t:ℝ)-d.sig*d.N

noncomputable def prefixLowMaximum (d : PositiveDistanceData) : ℝ :=
  finiteEnergyMaximum d.prefixLowDepths
    (fun v => ({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellSeparatedTerms
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace PositiveDistanceData

noncomputable def inverseDistanceEndpointKernel (d : PositiveDistanceData) (j : ℕ)
    (k : PairMaskIndex → ℕ) (r : ℝ) (z : Plane × Plane) : ℂ :=
  ((((dist z.1 z.2/(2:ℝ)^(-(d.a:ℝ)))⁻¹)^j:ℝ):ℂ) *
    sourceDistanceKernel
      (sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y)))
      (d.inverseEndpointSymbol k 0) (d.inverseEndpointSymbol k 1) r z.1 z.2

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellMixture
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

noncomputable def inversePhasedForm (d : PositiveDistanceData)
    (k : PairMaskIndex → ℕ) (ξ : Plane) : ℝ → ℂ :=
  sourceParentDistanceF (d.Q.descendant d.X) (d.Q.descendant d.Y)
    d.ρ d.ρ d.levelMass d.levelMass
    (spatialPhasedSymbol ((2:ℝ)^(-(d.a:ℝ))) ξ (d.inverseEndpointSymbol k 0))
    (spatialPhasedSymbol ((2:ℝ)^(-(d.a:ℝ))) ξ (d.inverseEndpointSymbol k 1))

noncomputable def inverseSpatialMixture (d : PositiveDistanceData) (j : ℕ)
    (k : PairMaskIndex → ℕ) (r : ℝ) : ℂ :=
  ∫ ξ, spatialFourierCoeff 96 2004 (by norm_num) (by norm_num) j ξ * d.inversePhasedForm k ξ r

noncomputable def inversePhasedBound (d : PositiveDistanceData) (j : ℕ) : ℝ :=
  (1*(symbolDerivativeConstant (2*j)^(2*j))*(symbolDerivativeConstant (2*j)^(2*j))*
    sourceArcLength.real univ) * ((d.ρ (d.Q.descendant d.X).carrier).toReal/d.levelMass)*
    ((d.ρ (d.Q.descendant d.Y).carrier).toReal/d.levelMass)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellOrderForm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace PositiveDistanceData

noncomputable def inverseOrderForm (d : PositiveDistanceData) (j : ℕ) (v r : ℝ) : ℂ :=
  ((inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)).map (fun b =>
    d.absorbedInverseCoefficient j v b*d.inverseSpatialMixture j b.2 r)).sum

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellParentEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

noncomputable def inversePhasedHF (d : PositiveDistanceData) (v : ℝ) (Ψ : ℝ → ℝ)
    (k : PairMaskIndex → ℕ) (ξ : Plane) : ℝ≥0∞ :=
  sourceParentHF d.a v Ψ (d.Q.descendant d.X) (d.Q.descendant d.Y)
    d.ρ d.ρ d.levelMass d.levelMass
    (spatialPhasedSymbol ((2:ℝ)^(-(d.a:ℝ))) ξ (d.inverseEndpointSymbol k 0))
    (spatialPhasedSymbol ((2:ℝ)^(-(d.a:ℝ))) ξ (d.inverseEndpointSymbol k 1))

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellSupremum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

noncomputable def inverseShellEnergies (d : PositiveDistanceData) (n : ℕ)
    (v : ℝ) (Ψ : ℝ → ℝ) : Set ℝ :=
  insert 0 {h | ∃ j ∈ Finset.range (n+1),
    ∃ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList),
    ∃ ξ, h = (d.inversePhasedHF v Ψ b.2 ξ).toReal}

noncomputable def inverseShellSupremum (d : PositiveDistanceData) (n : ℕ)
    (v : ℝ) (Ψ : ℝ → ℝ) : ℝ := sSup (d.inverseShellEnergies n v Ψ)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixRetainedPairs
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

noncomputable def suffixRectangles (d : PositiveDistanceData) (p : ℕ) : Finset (CellPath × CellPath) :=
  (projectionTestCells d.Q d.ρ d.a p d.X).product (projectionTestCells d.Q d.ρ d.a p d.Y)

noncomputable def suffixRetained (d : PositiveDistanceData) (p : ℕ) : Finset (CellPath × CellPath) := by
  classical
  exact (d.suffixRectangles p).filter fun c =>
    ∃ x ∈ (d.Q.descendant c.1).carrier, ∃ y ∈ (d.Q.descendant c.2).carrier, (x,y) ∈ d.good

abbrev suffixData (d : PositiveDistanceData) (c : CellPath × CellPath) : PositiveDistanceData :=
  {d with X := c.1,Y := c.2}

noncomputable def suffixFullDistance (d : PositiveDistanceData) (c : CellPath × CellPath) : Measure ℝ :=
  Measure.map (fun z : Plane × Plane => dist z.1 z.2) (d.suffixData c).cellPair

instance suffixFullDistance_finite (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (c : CellPath × CellPath) : IsFiniteMeasure (d.suffixFullDistance c) := by
  unfold suffixFullDistance
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchAnalyticSuccessors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

namespace AngularStateData

def branchState (d : AngularStateData) : BranchState := .H d.a₀ d.t₀ d.a d.v d.i

end AngularStateData

namespace PositiveDistanceData

def branchState (d : PositiveDistanceData) : BranchState := .D d.a d.t d.i
noncomputable def branchProfile (d : PositiveDistanceData) (n : ℕ) : ℝ := d.mass n-(n:ℝ)/d.N

def angularSuccessor (d : PositiveDistanceData) (p v : ℕ) (row : CellPath × CellPath) : AngularStateData :=
  ⟨d.Q,d.ρ,d.mass,d.N,d.q,d.a,d.t,p,v,d.J,d.i,d.lam,d.sig,row.1,row.2⟩

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ReachedStateRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

def extend (b : PolicyBranch A N q sig n) {u : BranchState} {l : BranchLabel}
    (hu : u.Valid N sig) (hstep : BranchStep A N q sig (b.state n) l u) :
    PolicyBranch A N q sig (n+1) where
  state j := if j ≤ n then b.state j else u
  label j := if j < n then b.label j else l
  valid j hj := by
    split_ifs with h
    · exact b.valid j h
    · exact hu
  step j hj := by
    by_cases h : j < n
    · simpa only [ite_eq_left h, ite_eq_left (show j ≤ n by omega),
        ite_eq_left (show j+1 ≤ n by omega)] using b.step j h
    · have he : j = n := by omega
      subst j
      simpa using hstep

@[simp] theorem extend_state_le (b : PolicyBranch A N q sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) {j : ℕ} (hj : j ≤ n) :
    (b.extend hu hstep).state j = b.state j := ite_eq_left hj

@[simp] theorem extend_label_lt (b : PolicyBranch A N q sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) {j : ℕ} (hj : j < n) :
    (b.extend hu hstep).label j = b.label j := ite_eq_left hj

end PolicyBranch

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_RecursiveCellInvariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

namespace PositiveDistanceData

def RecursiveCells (d : PositiveDistanceData) : Prop :=
  d.X.length = d.a ∧ d.Y.length = d.a ∧
  100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ∧
  dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ))

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_RecursiveEnergyFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

structure RecursiveEnvironment where
  Q : DyadicSquare
  ρ : Measure Plane
  mass : ℝ → ℝ
  N : ℕ
  q : ℕ
  J : ℕ
  lam : ℝ
  sig : ℝ

namespace RecursiveEnvironment

noncomputable def profile (e : RecursiveEnvironment) (n : ℕ) : ℝ := e.mass n-(n:ℝ)/e.N

def distanceData (e : RecursiveEnvironment) (a t i : ℕ) (X Y : CellPath) : PositiveDistanceData :=
  ⟨e.Q,e.ρ,e.mass,e.N,e.q,a,t,e.lam,e.sig,e.J,i,X,Y⟩

def angularData (e : RecursiveEnvironment) (a₀ t₀ a v i : ℕ) (X Y : CellPath) : AngularStateData :=
  ⟨e.Q,e.ρ,e.mass,e.N,e.q,a₀,t₀,a,v,e.J,i,e.lam,e.sig,X,Y⟩

def energies (e : RecursiveEnvironment) (K : ℕ) (Ψ : ℝ → ℝ) : BranchState → ℝ → Prop
  | .D a t i, x => ∃ X Y : CellPath,
      (e.distanceData a t i X Y).RecursiveCells ∧
      x = (e.distanceData a t i X Y).coincidence.toReal
  | .H a₀ t₀ a v i, x => ∃ X Y : CellPath, X.length = a ∧ Y.length = a ∧
      ∃ k : Fin 2 → PolicyDescriptor → ℕ,
        (∀ l, ∑ b ∈ (e.angularData a₀ t₀ a v i X Y).retainedList a, k l b ≤ K) ∧
      ∃ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) ∧
        (∀ l y, ‖h l y‖ ≤ 1) ∧ x = ((e.angularData a₀ t₀ a v i X Y).energy k h Ψ).toReal

end RecursiveEnvironment

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ReachedBranchWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

noncomputable def exponentSum (b : PolicyBranch A N q sig n) (lam eps : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1))

noncomputable def weight (b : PolicyBranch A N q sig n) (lam eps : ℝ) : ℝ :=
  ((2:ℝ)^N)^(b.exponentSum lam eps)

end PolicyBranch

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_TwoProfileRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

namespace RecursiveEnvironment

noncomputable def endpointTransform (e : RecursiveEnvironment) (c : ℕ) (X : CellPath)
    (k : PolicyDescriptor → ℕ) (h : Plane → ℂ) (z : ℝ × UnitCircle) : ℂ :=
  sourceAngularTransform e.ρ (e.Q.descendant X).carrier (((2:ℝ)^e.N)^(-e.mass c))
    (inheritedCircleSymbol ((e.angularData c e.N c e.N 0 X X).retainedList c) id k
      e.Q e.ρ e.mass e.N e.lam e.sig e.J 0 h) z.1 z.2

end RecursiveEnvironment

end PlanarFalconer

end OAI
end


