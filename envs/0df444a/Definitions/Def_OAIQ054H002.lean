-- Prove2me | Definitions.Def_OAIQ054H002
-- name    : OAIQ054H002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:46:33.237674+00:00
-- url     : https://prove2.me/theorems/db5fc1ab-6471-43f4-981f-069d33695063
-- title:
--   Definitions bundle OAIQ054H002 of the split of OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 457 declarations of OpenAI's Lean: 290 definitions, 36 instances and 131 theorems. The definitions and types are `OAI.HardSphere.Groups.certificateBad`, `OAI.HardSphere.Groups.datumCollisionBound`, `OAI.HardSphere.Groups.datumPhysicalReference`, `OAI.HardSphere.Groups.eligibleList`, `OAI.HardSphere.Groups.fieldLabelImage`, `OAI.HardSphere.Groups.fieldLabels`, `OAI.HardSphere.Groups.fieldRouteLabels`, `OAI.HardSphere.Groups.fullFailure`, `OAI.HardSphere.Groups.gridAllocationKernel`, `OAI.HardSphere.Groups.gridCube`, `OAI.HardSphere.Groups.gridShift`, `OAI.HardSphere.Groups.gridSite`, `OAI.HardSphere.Groups.latticeDatumBad`, `OAI.HardSphere.Groups.physicalAllocationKernel`, `OAI.HardSphere.Groups.physicalAverageLikelihood`, `OAI.HardSphere.Groups.physicalBathKernel`, `OAI.HardSphere.Groups.physicalBranchDatum`, `OAI.HardSphere.Groups.physicalBranchLaw`, `OAI.HardSphere.Groups.physicalCellPost`, `OAI.HardSphere.Groups.physicalCellVolumePost`, `OAI.HardSphere.Groups.physicalCodeObserver`, `OAI.HardSphere.Groups.physicalCodeTag`, `OAI.HardSphere.Groups.physicalCodedRoute`, `OAI.HardSphere.Groups.physicalCommonObserved`, `OAI.HardSphere.Groups.physicalDatum`, `OAI.HardSphere.Groups.physicalDatumLaw`, `OAI.HardSphere.Groups.physicalFamilyReference`, `OAI.HardSphere.Groups.physicalFullMidpoint`, `OAI.HardSphere.Groups.physicalGoodLikelihood`, `OAI.HardSphere.Groups.physicalGroupReference`, `OAI.HardSphere.Groups.physicalLabelAt`, `OAI.HardSphere.Groups.physicalLabels`, `OAI.HardSphere.Groups.physicalMixedRoutes`, `OAI.HardSphere.Groups.physicalObservedMixture`, `OAI.HardSphere.Groups.physicalObservedReference`, `OAI.HardSphere.Groups.physicalOnPrimary`, `OAI.HardSphere.Groups.physicalPairedRoute`, `OAI.HardSphere.Groups.physicalPrimaryReference`, `OAI.HardSphere.Groups.physicalRead`, `OAI.HardSphere.Groups.physicalRecoveredMidpoint` and 250 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/HardSphere, in whole or in part: `HardSphere_Allocation_AllocatedLinearity`, `HardSphere_Allocation_Allocation`, `HardSphere_Allocation_CertificateSix`, `HardSphere_Allocation_CoarsePhysical`, `HardSphere_Allocation_PhysicalAmbientRN`, `HardSphere_Allocation_PhysicalAverageMoment`, `HardSphere_Allocation_PhysicalBranchEstimates`, `HardSphere_Allocation_PhysicalBranchLaw`, `HardSphere_Allocation_PhysicalDatum`, `HardSphere_Allocation_PhysicalFamilyLikelihood`, `HardSphere_Allocation_PhysicalGroupComparison`, `HardSphere_Allocation_PhysicalLabelLaw`, `HardSphere_Allocation_PhysicalLifted`, `HardSphere_Allocation_PhysicalMidpointReference`, `HardSphere_Allocation_PhysicalMixedObservation`, `HardSphere_Allocation_PhysicalObservedMass`, `HardSphere_Allocation_PhysicalObservedMixture`, `HardSphere_Allocation_PhysicalPairedRoute`, `HardSphere_Allocation_PhysicalPrimary`, `HardSphere_Allocation_PhysicalReferenceRaw`, `HardSphere_Allocation_PhysicalRouteFactors`, `HardSphere_Allocation_PhysicalRouteGeometry`, `HardSphere_Allocation_PhysicalSupply`, `HardSphere_Allocation_PhysicalTaggedDensity`, `HardSphere_Allocation_PhysicalTaggedObservation`, `HardSphere_Allocation_PhysicalVertex`, `HardSphere_Allocation_RouteFields`, `HardSphere_Allocation_WeightedExpose`, `HardSphere_Bridges_BridgeBlocks`, `HardSphere_Bridges_BridgeResidual`, `HardSphere_Bridges_GroundBridge`, `HardSphere_Bridges_Index`, `HardSphere_Bridges_Moment8`, `HardSphere_Bridges_NormalizedPrefix`, `HardSphere_Bridges_PartialIndex`, `HardSphere_Bridges_PhaseBridge`, `HardSphere_Bridges_PhysicalEndpoint`, `HardSphere_Bridges_TorusLocalBridge`, `HardSphere_Bridges_WienerGaussian`, `HardSphere_Collisions_PhysicalCollision`, `HardSphere_Comparison_KilledLaplace`, `HardSphere_Comparison_PhysicalObservedLaw`, `HardSphere_Comparison_SafeMass`, `HardSphere_Conditioning_PairFiber`, `HardSphere_Conditioning_PartialAlgebra`, `HardSphere_Conditioning_Phase`, `HardSphere_Conditioning_PhaseMeasure`, `HardSphere_Conditioning_PhysicalObservation`, `HardSphere_Conditioning_PhysicalRoute`, `HardSphere_Conditioning_ReverseConfigurationPath`, `HardSphere_Conditioning_UnitPairCount`, `HardSphere_Conditioning_WeightedUnitPairCount`, `HardSphere_Cutoffs_CloseLabels`, `HardSphere_Cutoffs_CubicMoment`, `HardSphere_Cutoffs_MeshEvents`, `HardSphere_Cutoffs_Near`, `HardSphere_Cutoffs_PathLift`, `HardSphere_Cutoffs_RawAngleLift`, `HardSphere_Cutoffs_Regularize`, `HardSphere_Cutoffs_ThreeTorus`, `HardSphere_FormDomain_Basic`, `HardSphere_FormDomain_HilbertJet`, `HardSphere_FormDomain_Slice`, `HardSphere_Fourier_ArgumentAdd`, `HardSphere_Fourier_CharacterDerivativeFactor`, `HardSphere_Geometry_AddedSites`, `HardSphere_Geometry_AllowedProjection`, `HardSphere_Geometry_AnimalFamily`, `HardSphere_Geometry_BadGraph`, `HardSphere_Geometry_BufferedAllowed`, `HardSphere_Geometry_CenteredCircleLift`, `HardSphere_Geometry_ConfigurationPath`, `HardSphere_Geometry_CoordinateLine`, `HardSphere_Geometry_CubeCell`, `HardSphere_Geometry_EndpointDanger`, `HardSphere_Geometry_EuclideanTorus`, `HardSphere_Geometry_ExpWeightedMultiplier`, `HardSphere_Geometry_FirstVariation`, `HardSphere_Geometry_FlattenLinear`, `HardSphere_Geometry_FreePathExpectation`, `HardSphere_Geometry_GridActivePenalty`, `HardSphere_Geometry_GridAlignment`, `HardSphere_Geometry_GridAllocation`, `HardSphere_Geometry_GroundPathWeight`, `HardSphere_Geometry_GroundPositionLaw`, `HardSphere_Geometry_HalfShiftCover`, `HardSphere_Geometry_HeadLift`, `HardSphere_Geometry_HeatScalar`, `HardSphere_Geometry_InjectiveNear`, `HardSphere_Geometry_JoinConfiguration`, `HardSphere_Geometry_KilledObservable`, `HardSphere_Geometry_LocalCloseLabels`, `HardSphere_Geometry_LocalizedNearLabels`, `HardSphere_Geometry_MollifiedCloseCountMultiplier`, `HardSphere_Geometry_MollifiedCloseJoint`, `HardSphere_Geometry_PartitionErrorIntegral`, `HardSphere_Geometry_PathPermutation`, `HardSphere_Geometry_PointFin`, `HardSphere_Geometry_RadiusLaw`, `HardSphere_Geometry_RawAngleLift`, `HardSphere_Geometry_ScalarNormSqIntegral`, `HardSphere_Geometry_ScalarPartitionIms`, `HardSphere_Geometry_SelectedEnergyAddCompl`, `HardSphere_Geometry_SelectedUnitCellPenalty`, `HardSphere_Geometry_SimplePath`, `HardSphere_Geometry_SiteGroups`, `HardSphere_Geometry_SliceNormSq`, `HardSphere_Geometry_SmoothMultiplier`, `HardSphere_Geometry_SmoothSiteWeight`, `HardSphere_Geometry_SpatialPartitionEnergy`, `HardSphere_Geometry_SqTwiceSqAbs`, `HardSphere_Geometry_StarGraph`, `HardSphere_Geometry_TestVector`, `HardSphere_Geometry_TorusBall`, `HardSphere_Geometry_TorusLiftBox`, `HardSphere_Geometry_TorusNear`, `HardSphere_Geometry_UnitCenter`, `HardSphere_Geometry_Vertex`, `HardSphere_Operators_FreeTransition`, `HardSphere_Operators_Stationary`, `HardSphere_Orbitals_FieldApply`, `HardSphere_Orbitals_FreePathLawFiniteDeletion`, `HardSphere_PathBounds_ConfigurationTailLp`, `HardSphere_PathBounds_InteractingVisits`, `HardSphere_PathBounds_LatticeExponentialSum`, `HardSphere_PathBounds_PathTailConstant`, `HardSphere_PathBounds_ShiftInteracting`, `HardSphere_Paths_SimpleRouteGeometry`, `HardSphere_Rescaling_PhysicalRescaling`, `HardSphere_Rescaling_PhysicalUnitary`, `HardSphere_Thermodynamics_PhysicalRescaleDomain`, `HardSphere_Thermodynamics_PhysicalRescaleLp`.
--
--   **Imports.** It imports the published bundle `Def_HardSphere`; the bundles `OAIQ054H000` and `OAIQ054H001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.HardSphere.BathSlice.IsGroundVector.bathLaw_ae_allowed`, `OAI.HardSphere.BathSlice.physical_close_tail`, `OAI.HardSphere.CellOrbital.grid_stationary_low_above`, `OAI.HardSphere.Groups.canonical_supply_counts`, `OAI.HardSphere.Groups.grid_close_tail`, `OAI.HardSphere.Groups.physicalBranchLaw_collision`, `OAI.HardSphere.Groups.physicalObservedMixture_mass`, `OAI.HardSphere.Groups.physicalPairedRoute_marginals`, `OAI.HardSphere.Groups.physicalPairedRoute_midpoint`, `OAI.HardSphere.Groups.physicalSharedOn_mass`, `OAI.HardSphere.Groups.physicalTagged_observed_moment`, `OAI.HardSphere.Groups.physical_common_observed_estimates`, `OAI.HardSphere.Groups.physical_first_likelihood_moment`, `OAI.HardSphere.Groups.physical_ground_bad_supply`, `OAI.HardSphere.Groups.physical_group_common_comparison`, `OAI.HardSphere.Groups.physical_modulus_from_gains`, `OAI.HardSphere.Groups.physical_second_likelihood_moment`, `OAI.HardSphere.IsGroundVector.ae_killed_complexPhase`, `OAI.HardSphere.IsGroundVector.groundPathLaw_marginal`, `OAI.HardSphere.IsGroundVector.groundPathLaw_probability`, `OAI.HardSphere.ShiftVisits.ground_excessVisitors_tail`, `OAI.HardSphere.ShiftVisits.ground_longVisitors_tail`, `OAI.HardSphere.ShiftVisits.interacting_visit_mgf_uniform`, `OAI.HardSphere.ground_product_one_add`, `OAI.HardSphere.killedLaplace_graph`, `OAI.HardSphere.killedTransition_norm_le_of_energy`, `OAI.HardSphere.spatial_localized_form`, `OAI.HardSphere.spatial_spectral_average` and `OAI.HardSphere.weighted_count_penalty`; the proofs of `OAI.HardSphere.BathSlice.IsGroundVector.bathLaw_ae_allowed`, `OAI.HardSphere.BathSlice.physical_close_tail`, `OAI.HardSphere.Bridge.physical_failure_sum`, `OAI.HardSphere.CellOrbital.grid_stationary_low_above`, `OAI.HardSphere.CellOrbital.physical_deficiency`, `OAI.HardSphere.Groups.PhysicalRouteAux.path_bounds`, `OAI.HardSphere.Groups.canonical_supply_counts`, `OAI.HardSphere.Groups.grid_close_tail`, `OAI.HardSphere.Groups.physicalBranchLaw_collision`, `OAI.HardSphere.Groups.physicalObservedMixture_mass`, `OAI.HardSphere.Groups.physicalPairedRoute_marginals`, `OAI.HardSphere.Groups.physicalPairedRoute_midpoint`, `OAI.HardSphere.Groups.physicalRouteAux_nonempty`, `OAI.HardSphere.Groups.physicalSharedOn_mass`, `OAI.HardSphere.Groups.physicalTagged_observed_moment`, `OAI.HardSphere.Groups.physical_common_observed_estimates`, `OAI.HardSphere.Groups.physical_first_likelihood_moment`, `OAI.HardSphere.Groups.physical_ground_bad_supply`, `OAI.HardSphere.Groups.physical_group_common_comparison`, `OAI.HardSphere.Groups.physical_modulus_from_gains`, `OAI.HardSphere.Groups.physical_second_likelihood_moment`, `OAI.HardSphere.IsGroundVector.ae_killed_complexPhase`, `OAI.HardSphere.IsGroundVector.groundPathLaw_marginal`, `OAI.HardSphere.IsGroundVector.groundPathLaw_probability`, `OAI.HardSphere.ShiftVisits.ground_excessVisitors_tail`, `OAI.HardSphere.ShiftVisits.ground_longVisitors_tail`, `OAI.HardSphere.ShiftVisits.interacting_visit_mgf_uniform`, `OAI.HardSphere.condensation_with_mixed`, `OAI.HardSphere.ground_product_one_add`, `OAI.HardSphere.killedLaplace_graph`, `OAI.HardSphere.killedTransition_norm_le_of_energy`, `OAI.HardSphere.physical_uniform_phase_error`, `OAI.HardSphere.spatial_localized_form`, `OAI.HardSphere.spatial_spectral_average` and `OAI.HardSphere.weighted_count_penalty`.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/HardSphere at commit adc7f12

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H000
import Definitions.Def_OAIQ054H001

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_Index
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Wiener.instIsProbabilityMeasureContinuousMapElemRealTimeBridgeLaw _root_.OAI.HardSphere.configurationPathBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def badLevel (n : ℕ) : Set Noise :=
  {ω | ∃ k : Fin (2 ^ n), (4/3 : ℝ) ^ n ≤ |ω (.inr ⟨n, k⟩)|}

instance instIsProbabilityMeasureContinuousMapElemRealTimeWiener : IsProbabilityMeasure wiener := by unfold wiener; exact Measure.isProbabilityMeasure_map measurable_path.aemeasurable

def hatKernel (n : ℕ) (s t : ℝ) : ℝ := ∑ k : Fin (2^n), tent n k s * tent n k t

def partialBridge (n : ℕ) (s t : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n, weight m * hatKernel m s t

end HardSphere.Wiener
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PartialIndex
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.configurationPathBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def partialEmbed (n : ℕ) : PartialIndex n → Index
  | .inl u => .inl u
  | .inr ⟨m,k⟩ => .inr ⟨m.val,k⟩

def coefficient (n : ℕ) (t : ℝ) : PartialIndex n → ℝ
  | .inl _ => t
  | .inr ⟨m,k⟩ => amplitude m.val * tent m.val k t

def partialPath (n : ℕ) (ω : Noise) : C(Time,ℝ) :=
  ω (.inl ()) • ⟨fun t ↦ t.val, continuous_subtype_val⟩ +
    ∑ m ∈ Finset.range n, level m ω

def denseEval (f : C(Time,ℝ)) : ℕ → ℝ := fun n ↦ f (TopologicalSpace.denseSeq Time n)

end HardSphere.Wiener
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_Basic
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere

lemma measurePreserving_permute {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (permuteConfiguration (L := L) σ) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin N ↦ Torus L) σ.symm
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext X i
  simp [permuteConfiguration, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

section

attribute [local instance] scalarL2_addCommMonoid scalarL2_module

def permutationPullback {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N)) :
    ScalarL2 N L →ₗ[ℂ] ScalarL2 N L :=
  Lp.compMeasurePreservingₗ ℂ _ (measurePreserving_permute σ)

end

section

attribute [local instance] scalarL2_normedAddCommGroup scalarL2_module

def bosonicSubmodule (N : ℕ) (L : Length) : Submodule ℂ (ScalarL2 N L) :=
  ⨅ σ : Equiv.Perm (Fin N),
    @LinearMap.ker ℂ ℂ (ScalarL2 N L) (ScalarL2 N L)
      Complex.instSemiring Complex.instSemiring
      (scalarL2_normedAddCommGroup N L).toAddCommMonoid
      (scalarL2_normedAddCommGroup N L).toAddCommMonoid
      (scalarL2_module N L) (scalarL2_module N L) (RingHom.id ℂ)
      (@HSub.hSub _ _ _
        (@instHSub _ (@LinearMap.instSub ℂ ℂ (ScalarL2 N L) (ScalarL2 N L)
          Complex.instSemiring Complex.instSemiring
          (scalarL2_normedAddCommGroup N L).toAddCommMonoid
          (scalarL2_normedAddCommGroup N L).toAddCommGroup
          (scalarL2_module N L) (scalarL2_module N L) (RingHom.id ℂ)))
        (permutationPullback σ)
        (@LinearMap.id ℂ (ScalarL2 N L) Complex.instSemiring
          (scalarL2_normedAddCommGroup N L).toAddCommMonoid (scalarL2_module N L)))

end

def groundFormSubmodule (N : ℕ) (L : Length) (a : ℝ) : Submodule ℂ (Jet N L) :=
  dirichletSubmodule N L a ⊓
    (bosonicSubmodule N L).comap (LinearMap.fst ℂ (ScalarL2 N L) (Direction N → ScalarL2 N L))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FirstVariation
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
namespace HardSphere

lemma allowed_iff_ne {N : ℕ} {L : Length} {a : ℝ} {X : Configuration N L} :
    X ∈ allowed N L a ↔ ∀ i j, i ≠ j → a < torusDistance L (X i) (X j) := by
  constructor
  · intro h i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact h i j hlt
    · simpa only [torusDistance_comm] using h j i hgt
  · intro h i j hij
    exact h i j (ne_of_lt hij)

lemma allowed_permute {N : ℕ} {L : Length} {a : ℝ}
    (σ : Equiv.Perm (Fin N)) (X : Configuration N L) :
    permuteConfiguration σ X ∈ allowed N L a ↔ X ∈ allowed N L a := by
  simp only [allowed_iff_ne, permuteConfiguration]
  constructor
  · intro h i j hij
    simpa using h (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij)
  · intro h i j hij
    exact h (σ i) (σ j) (σ.injective.ne hij)

lemma permuteLift_direction {N : ℕ} (σ : Equiv.Perm (Fin N)) (p : Direction N) :
    permuteLift σ (Pi.single p.1 (Pi.single p.2 1)) =
      Pi.single (σ.symm p.1) (Pi.single p.2 1) := by
  ext i j
  change (Pi.single p.1 (Pi.single p.2 (1 : ℝ)) : LiftedConfiguration N) (σ i) j = _
  by_cases h : i = σ.symm p.1
  · subst i; simp
  · have h' : σ i ≠ p.1 := fun hh ↦ h ((Equiv.eq_symm_apply σ).mpr hh)
    simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

lemma coordDerivative_permute {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest N L a) (σ : Equiv.Perm (Fin N)) (p : Direction N) :
    coordDerivative N L (f.toFun ∘ permuteConfiguration σ) p =
      coordDerivative N L f.toFun (σ.symm p.1, p.2) ∘ permuteConfiguration σ := by
  funext X
  change (fderiv ℝ ((fun Y ↦ f.toFun (project N L Y)) ∘ permuteLift σ)
    (representative N L X)) (Pi.single p.1 (Pi.single p.2 1)) = _
  rw [fderiv_comp _ (f.smooth.differentiable (by simp)).differentiableAt
    (permuteLift σ).differentiableAt, (permuteLift σ).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    permuteLift_direction]
  rfl

def SmoothTest.permute {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest N L a) (σ : Equiv.Perm (Fin N)) : SmoothTest N L a where
  toFun := f.toFun ∘ permuteConfiguration σ
  smooth := f.smooth.comp (permuteLift σ).contDiff
  compact := HasCompactSupport.of_compactSpace _
  support_allowed := by
    intro X hX
    apply (allowed_permute σ X).mp
    exact f.support_allowed
      (tsupport_comp_subset_preimage (f := permuteConfiguration σ) f.toFun (continuous_pi fun i ↦ continuous_apply (σ i)) hX)
  memLp := f.memLp.comp_measurePreserving (measurePreserving_permute σ)
  partial_memLp := by
    intro p
    rw [coordDerivative_permute]
    exact (f.partial_memLp (σ.symm p.1, p.2)).comp_measurePreserving
      (measurePreserving_permute σ)

section

attribute [local instance] scalarL2_addCommMonoid scalarL2_module

lemma continuous_permutationPullback_jet {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N)) :
    Continuous (fun u : Jet N L ↦ (permutationPullback σ u.1,
      fun direction : Direction N ↦
        permutationPullback σ (u.2 (σ.symm direction.1, direction.2)))) := by
  let pullback : ScalarL2 N L →ₗᵢ[ℂ] ScalarL2 N L :=
    Lp.compMeasurePreservingₗᵢ ℂ (permuteConfiguration σ) (measurePreserving_permute σ)
  exact (pullback.continuous.comp continuous_fst).prodMk
    (continuous_pi fun p ↦ pullback.continuous.comp ((continuous_apply _).comp continuous_snd))

def permutationJet {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N)) :
    Jet N L →L[ℂ] Jet N L where
  toFun u := (permutationPullback σ u.1,
    fun p ↦ permutationPullback σ (u.2 (σ.symm p.1, p.2)))
  map_add' _ _ := by simp [map_add]; rfl
  map_smul' _ _ := by simp [map_smul]; rfl
  cont := continuous_permutationPullback_jet σ

end

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_HilbertJet
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere

attribute [local instance] scalarL2_addCommMonoid scalarL2_module scalarL2_completeSpace

def hilbertDomain (N : ℕ) (L : Length) (a : ℝ) : Submodule ℂ (HilbertJet N L) :=
  (dirichletSubmodule N L a).comap (hilbertJetEquiv N L).toLinearMap

instance hilbertDomain_closed (N : ℕ) (L : Length) (a : ℝ) :
    IsClosed (hilbertDomain N L a : Set (HilbertJet N L)) :=
  (Submodule.isClosed_topologicalClosure _).preimage (hilbertJetEquiv N L).continuous
instance hilbertDomain_complete (N : ℕ) (L : Length) (a : ℝ) :
    CompleteSpace (hilbertDomain N L a) := IsClosed.completeSpace_coe

def scalarEmbedding (N : ℕ) (L : Length) (a : ℝ) :
    (hilbertDomain N L a) →L[ℂ] ScalarL2 N L :=
  (PiLp.proj _ _ none).comp (hilbertDomain N L a).subtypeL

def formResolvent (N : ℕ) (L : Length) (a : ℝ) : ScalarL2 N L →L[ℂ] ScalarL2 N L :=
  (scalarEmbedding N L a).comp (scalarEmbedding N L a).adjoint

lemma isOpen_allowed (N : ℕ) (L : Length) (a : ℝ) : IsOpen (allowed N L a) := by
  let P := {p : Fin N × Fin N // p.1 < p.2}
  have heq : allowed N L a = ⋂ p : P, {X : Configuration N L | a < torusDistance L (X p.1.1) (X p.1.2)} := by
    ext X
    simp only [allowed, mem_ofPred_eq, mem_iInter]
    exact ⟨fun h p ↦ h _ _ p.2, fun h i j hij ↦ h ⟨(i,j),hij⟩⟩
  rw [heq]
  apply isOpen_iInter_of_finite
  intro p
  have hc : Continuous (fun X : Configuration N L ↦ torusDistance L (X p.1.1) (X p.1.2)) := by
    unfold torusDistance
    fun_prop
  exact isOpen_lt continuous_const hc

end HardSphere

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ConfigurationPath
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Wiener.instIsProbabilityMeasureContinuousMapElemRealTimeBridgeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

lemma staysAllowed_open (N : ℕ) (L : Length) (a : ℝ) : IsOpen (staysAllowed N L a) :=
  ContinuousMap.isOpen_setOfPred_range_subset (isOpen_allowed N L a)

instance coordinateWiener_probability (N : ℕ) : IsProbabilityMeasure (coordinateWiener N) := by
  unfold coordinateWiener
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma freeTrajectory_continuous (N : ℕ) (L : Length) (s : ℝ) :
    Continuous (fun p : CoordinatePaths N × Configuration N L ↦ freeTrajectory N L s p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  unfold Function.uncurry
  change Continuous (fun p : (CoordinatePaths N × Configuration N L) × Time ↦
    fun i j ↦ p.1.2 i j + ((Real.sqrt (2*s) * p.1.1 (i,j) p.2 : ℝ) : AddCircle L.val))
  fun_prop

lemma freeTrajectory_marginal (N : ℕ) (L : Length) (s : ℝ) (t : Time) :
    MeasurePreserving (fun p : CoordinatePaths N × Configuration N L ↦ freeTrajectory N L s p.1 p.2 t)
      ((coordinateWiener N).prod volume) volume := by
  let : (volume : Measure (Torus L)).IsAddLeftInvariant := by
    rw [volume_pi]
    exact Measure.pi.isAddLeftInvariant _
  let : (volume : Measure (Configuration N L)).IsAddLeftInvariant := by
    rw [volume_pi]
    exact Measure.pi.isAddLeftInvariant _
  let : (volume : Measure (Configuration N L)).IsAddRightInvariant :=
    IsAddLeftInvariant.isAddRightInvariant
  have hm : Measurable (fun p : CoordinatePaths N × Configuration N L ↦ freeTrajectory N L s p.1 p.2 t) :=
    ((freeTrajectory_continuous N L s).eval continuous_const).measurable
  have hskew := (MeasurePreserving.id (coordinateWiener N)).skew_product hm
    (Filter.Eventually.of_forall (fun w : CoordinatePaths N ↦
      map_add_right_eq_self (volume : Measure (Configuration N L))
        (fun i j ↦ ((Real.sqrt (2*s) * w (i,j) t : ℝ) : AddCircle L.val))))
  exact (measurePreserving_snd (μ := coordinateWiener N) (ν := (volume : Measure (Configuration N L)))).comp hskew

lemma freePathLaw_marginal (N : ℕ) (L : Length) (s : ℝ) (t : Time) :
    MeasurePreserving (fun f : ConfigurationPath N L ↦ f t) (freePathLaw N L s) volume := by
  have he : Measurable (fun f : ConfigurationPath N L ↦ f t) :=
    (continuous_id.eval continuous_const).measurable
  refine ⟨he,?_⟩
  rw [freePathLaw,Measure.map_map he (freeTrajectory_continuous N L s).measurable]
  exact (freeTrajectory_marginal N L s t).map_eq

def killedPathLaw (N : ℕ) (L : Length) (a s : ℝ) : Measure (ConfigurationPath N L) :=
  (freePathLaw N L s).restrict (staysAllowed N L a)

end HardSphere

namespace HardSphere
open Wiener
open scoped ComplexConjugate

def endpointPull (N : ℕ) (L : Length) (t : ℝ) (s : Time) :
    ScalarL2 N L →ₗᵢ[ℂ] FreePathL2 N L t :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun ω : ConfigurationPath N L ↦ ω s)
    (freePathLaw_marginal N L t s)

lemma avoidanceIndicator_memLp (N : ℕ) (L : Length) (a t : ℝ) :
    MemLp ((staysAllowed N L a).indicator (fun _ ↦ (1:ℂ))) ∞ (freePathLaw N L t) := by
  exact MemLp.indicator (staysAllowed_open N L a).measurableSet (memLp_top_const (1:ℂ))

def avoidanceMultiplier (N : ℕ) (L : Length) (a t : ℝ) : FreePathL2 N L t →L[ℂ] FreePathL2 N L t :=
  L2Multiplier.clm _ (avoidanceIndicator_memLp N L a t)

def killedTransition (N : ℕ) (L : Length) (a t : ℝ) : ScalarL2 N L →L[ℂ] ScalarL2 N L :=
  (endpointPull N L t 0).toContinuousLinearMap.adjoint ∘L
    (avoidanceMultiplier N L a t ∘L (endpointPull N L t 1).toContinuousLinearMap)

end HardSphere

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_NormalizedPrefix
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
namespace Wiener

def normalizedPrefix (u : Time) : C(Time,ℝ) →L[ℝ] C(Time,ℝ) :=
  (Real.sqrt (u:ℝ))⁻¹ • prefixMap u

def normalizedSuffix (u : Time) : C(Time,ℝ) →L[ℝ] C(Time,ℝ) :=
  (Real.sqrt (1-(u:ℝ)))⁻¹ • suffixMap u

end Wiener

open Wiener

def splitTime (s t : ℝ) (hs : 0 < s) (ht : 0<t) : Time :=
  ⟨s/(s+t), (div_pos hs (add_pos hs ht)).le, (div_le_one (add_pos hs ht)).mpr (by linarith)⟩

def configurationPrefix (N : ℕ) (L : Length) (u : Time) (ω : ConfigurationPath N L) :
    ConfigurationPath N L := ω.comp (prefixTime u)

def configurationSuffix (N : ℕ) (L : Length) (u : Time) (ω : ConfigurationPath N L) :
    ConfigurationPath N L := ω.comp (suffixTime u)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_ReverseConfigurationPath
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open Wiener
open scoped ComplexConjugate

lemma reverseConfigurationPath_continuous (N : ℕ) (L : Length) :
    Continuous (reverseConfigurationPath N L) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath N L × Time ↦ p.1 (reverseTime p.2))
  fun_prop

def reversePathEquiv (N : ℕ) (L : Length) : ConfigurationPath N L ≃ᵐ ConfigurationPath N L where
  toFun := reverseConfigurationPath N L
  invFun := reverseConfigurationPath N L
  left_inv := reverseConfigurationPath_reverse N L
  right_inv := reverseConfigurationPath_reverse N L
  measurable_toFun := (reverseConfigurationPath_continuous N L).measurable
  measurable_invFun := (reverseConfigurationPath_continuous N L).measurable

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CoordinateLine
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

lemma SmoothTest.continuous {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    Continuous f.toFun := continuous_of_continuous_lift f.smooth.continuous

lemma SmoothTest.continuous_partial {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest N L a) (p : Direction N) :
    Continuous (coordDerivative N L f.toFun p) := continuous_coordDerivative f.smooth p

def coordinateLine {N : ℕ} {L : Length} (X : Configuration N L)
    (p : Direction N) (t : AddCircle L.val) : Configuration N L :=
  X + Pi.single p.1 (Pi.single p.2 t)

lemma project_coordinateLine {N : ℕ} {L : Length} (X : Configuration N L)
    (p : Direction N) (t : ℝ) :
    project N L (representative N L X + t • (Pi.single p.1 (Pi.single p.2 1) : LiftedConfiguration N)) =
      coordinateLine X p (t : AddCircle L.val) := by
  rw [project_add, project_representative]
  congr 1
  funext i j
  by_cases hi : i = p.1 <;> by_cases hj : j = p.2 <;>
    simp [project, hi, hj]

lemma hasDerivAt_coordinateLine {N : ℕ} {L : Length} {f : Configuration N L → ℂ}
    (hf : Differentiable ℝ (fun X : LiftedConfiguration N ↦ f (project N L X)))
    (X : Configuration N L) (p : Direction N) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (coordinateLine X p (s : AddCircle L.val)))
      (coordDerivative N L f p (coordinateLine X p (t : AddCircle L.val))) t := by
  let e : LiftedConfiguration N := Pi.single p.1 (Pi.single p.2 1)
  have he : HasDerivAt (fun s : ℝ ↦ representative N L X + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add (representative N L X)
  have h := (hf (representative N L X + t • e)).hasFDerivAt.comp_hasDerivAt t he
  have hfun : (fun s : ℝ ↦ f (project N L (representative N L X + s • e))) =
      (fun s : ℝ ↦ f (coordinateLine X p (s : AddCircle L.val))) := by
    funext s
    rw [project_coordinateLine]
  change HasDerivAt (fun s ↦ f (project N L (representative N L X + s • e)))
    (fderiv ℝ (fun Y ↦ f (project N L Y)) (representative N L X + t • e) e) t at h
  rw [hfun] at h
  rw [← coordDerivative_project f p (representative N L X + t • e),
    project_coordinateLine] at h
  exact h

open scoped ComplexConjugate

section

local instance configurationContinuousMapStarModule (N : ℕ) (L : Length) :
    StarModule ℂ C(Configuration N L, ℂ) := inferInstance

attribute [local instance] OAI.HardSphere.complexTopologicalSemiring
def smoothAlgebra (N : ℕ) (L : Length) : StarSubalgebra ℂ C(Configuration N L, ℂ) where
  carrier := {f | ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun X : LiftedConfiguration N ↦ f (project N L X))}
  mul_mem' := by
    intro f g hf hg
    simp only [Set.mem_ofPred_eq] at *
    exact hf.mul hg
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_ofPred_eq] at *
    exact hf.add hg
  algebraMap_mem' := by
    intro c
    simp only [Set.mem_ofPred_eq, algebraMap_apply]
    exact contDiff_const
  star_mem' := by
    intro f hf
    simp only [Set.mem_ofPred_eq] at *
    exact Complex.conjCLE.contDiff.comp hf
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, ContinuousMap.zero_apply]
    exact contDiff_const
  one_mem' := by
    simp only [Set.mem_ofPred_eq, ContinuousMap.one_apply]
    exact contDiff_const

end

def coordinateCharacter {N : ℕ} {L : Length} (p : Direction N) : C(Configuration N L, ℂ) :=
  (fourier 1).comp ⟨fun X ↦ X p.1 p.2,
    (continuous_apply p.2).comp (continuous_apply p.1)⟩

def smoothPartial {N : ℕ} {L : Length} (f : smoothAlgebra N L) (p : Direction N) :
    C(Configuration N L, ℂ) :=
  ⟨coordDerivative N L f.val p, continuous_coordDerivative f.property p⟩

section

local instance configurationProductBorel (N : ℕ) (L : Length) :
    BorelSpace (Configuration N L) := Pi.borelSpace

end

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_Slice
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Filter Set

lemma smooth_insertNth {n : ℕ} (j : Fin (n+1)) (x : Fin 3 → ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun Y : LiftedConfiguration n ↦ Fin.insertNth (α := fun _ ↦ Fin 3 → ℝ) j x Y) := by
  apply contDiff_pi.mpr
  intro i
  induction i using j.succAboveCases with
  | x => simpa only [Fin.insertNth_apply_same] using
      (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : LiftedConfiguration n ↦ x))
  | p i => simpa only [Fin.insertNth_apply_succAbove] using
      (contDiff_apply ℝ (Fin 3 → ℝ) i)

lemma smooth_slice {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest (n+1) L a)
    (j : Fin (n+1)) (x : Torus L) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun Y : LiftedConfiguration n ↦ f.toFun (j.insertNth x (project n L Y))) := by
  have h := f.smooth.comp (smooth_insertNth j (representative 1 L (fun _ ↦ x) 0))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext Y
  congr 1
  ext i q
  induction i using j.succAboveCases with
  | x =>
    simp only [project,Fin.insertNth_apply_same]
    exact (congr_fun (congr_fun (project_representative 1 L (fun _ ↦ x)) 0) q).symm
  | p i => simp only [project,Fin.insertNth_apply_succAbove]

lemma insertNth_coordinateLine {n : ℕ} {L : Length} (j : Fin (n+1)) (x : Torus L)
    (Y : Configuration n L) (p : Direction n) (t : AddCircle L.val) :
    j.insertNth x (coordinateLine Y p t)=coordinateLine (j.insertNth x Y) (j.succAbove p.1,p.2) t := by
  ext i q
  induction i using j.succAboveCases with
  | x => simp [coordinateLine]
  | p i => simp [coordinateLine,Pi.single_apply,Fin.succAbove_inj]

lemma coordDerivative_slice {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest (n+1) L a)
    (j : Fin (n+1)) (x : Torus L) (p : Direction n) :
    coordDerivative n L (fun Y ↦ f.toFun (j.insertNth x Y)) p=
      fun Y ↦ coordDerivative (n+1) L f.toFun (j.succAbove p.1,p.2) (j.insertNth x Y) := by
  funext Y
  have h1 := hasDerivAt_coordinateLine (f := fun Y ↦ f.toFun (j.insertNth x Y)) ((smooth_slice f j x).differentiable (by simp)) Y p 0
  have h2 := hasDerivAt_coordinateLine (f.smooth.differentiable (by simp))
    (j.insertNth x Y) (j.succAbove p.1,p.2) 0
  simp only [insertNth_coordinateLine] at h1
  have h := h1.unique h2
  simpa [coordinateLine] using h

def SmoothTest.slice {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest (n+1) L a)
    (j : Fin (n+1)) (x : Torus L) : SmoothTest n L a where
  toFun Y := f.toFun (j.insertNth x Y)
  smooth := smooth_slice f j x
  compact := HasCompactSupport.of_compactSpace _
  support_allowed := by
    intro Y hY i k hik
    have h := f.support_allowed (tsupport_comp_subset_preimage f.toFun
      (Continuous.finInsertNth j (continuous_const : Continuous (fun _ : Configuration n L ↦ x)) continuous_id) hY)
    simpa only [Fin.insertNth_apply_succAbove,id_eq] using h (j.succAbove i) (j.succAbove k)
      (Fin.strictMono_succAbove j hik)
  memLp := (f.continuous.comp (Continuous.finInsertNth j (continuous_const : Continuous (fun _ : Configuration n L ↦ x)) continuous_id)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  partial_memLp := fun p ↦ by
    rw [coordDerivative_slice]
    exact ((f.continuous_partial (j.succAbove p.1,p.2)).comp
      (Continuous.finInsertNth j (continuous_const : Continuous (fun _ : Configuration n L ↦ x)) continuous_id)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_ThreeTorus
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace PeriodicCutoff
variable (L : ℝ) [hL : Fact (0<L)]

def box (R : ℝ) (x : ThreeTorus L) : Set (ThreeTorus L) :=
  Set.univ.pi (fun j ↦ Metric.closedBall (x j) R)

def angle (r : ℝ) (y x : ThreeTorus L) : ℝ :=
  Real.pi/2*Real.smoothTransition ((pairQ L y x-2*r^2)/(2*r^2))

def angleLift (r : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  Real.pi/2*Real.smoothTransition ((qLift L z-2*r^2)/(2*r^2))

omit hL in
lemma angleLift_smooth (r : ℝ) : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (angleLift L r) := by
  have hq : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (qLift L) := by
    apply ContDiff.sum
    intro j _
    exact (chordLift_smooth L).comp (contDiff_apply ℝ ℝ j)
  exact contDiff_const.mul (Real.smoothTransition.contDiff.comp
    ((hq.sub contDiff_const).div_const _))

def angleFactor (r : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  Real.pi/(4*r^2)*deriv Real.smoothTransition ((qLift L z-2*r^2)/(2*r^2))

def anglePartial (r : ℝ) (z : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  angleFactor L r z*deriv (chordLift L) (z j)

end PeriodicCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SmoothMultiplier
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

def SmoothTest.multiply {N : ℕ} {L : Length} {a : ℝ} (f : SmoothMultiplier N L)
    (g : SmoothTest N L a) : SmoothTest N L a where
  toFun := f.toFun * g.toFun
  smooth := f.smooth.mul g.smooth
  compact := g.compact.mul_left
  support_allowed := tsupport_mul_subset_right.trans g.support_allowed
  memLp := g.memLp.mul f.memLp_top
  partial_memLp := by
    intro p
    rw [coordDerivative_mul (f.smooth.differentiable (by simp))
      (g.smooth.differentiable (by simp))]
    exact ((g.partial_memLp p).mul f.memLp_top).add
      ((f.partial_memLp_top p).mul g.memLp)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_ConfigurationTailLp
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

lemma configurationTail_preserving (n : ℕ) (L : Length) :
    MeasurePreserving (Fin.tail : Configuration (n+1) L → Configuration n L)
      volume ((volume (Set.univ : Set (Torus L))) • (volume : Measure (Configuration n L))) := by
  have h : MeasurePreserving (Prod.snd : Torus L × Configuration n L → Configuration n L)
      volume ((volume (Set.univ : Set (Torus L))) • (volume : Measure (Configuration n L))) :=
    ⟨measurable_snd,Measure.map_snd_prod⟩
  simpa only [Function.comp_def,MeasurableEquiv.piFinSuccAbove_apply,Fin.zero_succAbove,Fin.insertNthEquiv_zero,Fin.consEquiv_symm_apply] using
    h.comp (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0)

lemma configurationTail_quasiPreserving (n : ℕ) (L : Length) :
    Measure.QuasiMeasurePreserving (Fin.tail : Configuration (n+1) L → Configuration n L)
      volume volume := by
  refine ⟨(configurationTail_preserving n L).measurable,?_⟩
  rw [(configurationTail_preserving n L).map_eq]
  exact Measure.smul_absolutelyContinuous

lemma memLp_configurationTail {n : ℕ} {L : Length} {f : Configuration n L → ℂ}
    (hf : MemLp f 2 volume) : MemLp (fun X : Configuration (n+1) L ↦ f (Fin.tail X)) 2 volume :=
  (hf.smul_measure (measure_ne_top _ _)).comp_measurePreserving (configurationTail_preserving n L)

def configurationTailLp {n : ℕ} {L : Length} (u : ScalarL2 n L) : ScalarL2 (n+1) L :=
  (memLp_configurationTail (Lp.memLp u)).toLp _

lemma coe_configurationTailLp {n : ℕ} {L : Length} (u : ScalarL2 n L) :
    configurationTailLp u =ᵐ[volume] fun X ↦ u (Fin.tail X) := MemLp.coeFn_toLp _

def configurationTailLinear (n : ℕ) (L : Length) : ScalarL2 n L →ₗ[ℂ] ScalarL2 (n+1) L where
  toFun := configurationTailLp
  map_add' u v := by
    apply Lp.ext
    filter_upwards [coe_configurationTailLp (u+v),coe_configurationTailLp u,coe_configurationTailLp v,
      (configurationTail_quasiPreserving n L).ae_eq_comp (Lp.coeFn_add u v),
      Lp.coeFn_add (configurationTailLp u) (configurationTailLp v)] with X h1 h2 h3 h4 h5
    simp only [Function.comp_def,Pi.add_apply] at h4
    rw [h1,h4,h5,Pi.add_apply,h2,h3]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [coe_configurationTailLp (c • u),coe_configurationTailLp u,
      (configurationTail_quasiPreserving n L).ae_eq_comp (Lp.coeFn_smul c u),
      Lp.coeFn_smul c (configurationTailLp u)] with X h1 h2 h3 h4
    simp only [Function.comp_def,Pi.smul_apply] at h3
    simp only [h1,h3,h4,Pi.smul_apply,h2,RingHom.id_apply]

lemma norm_configurationTailLp {n : ℕ} {L : Length} (u : ScalarL2 n L) :
    ‖configurationTailLp u‖ = (volume (Set.univ : Set (Torus L)) ^ (1 / (2:ℝ))).toReal * ‖u‖ := by
  rw [configurationTailLp,Lp.norm_toLp]
  have he := eLpNorm_comp_measurePreserving (p:= (2:ℝ≥0∞))
    ((Lp.stronglyMeasurable u).aestronglyMeasurable
      (μ := volume univ • (volume : Measure (Configuration n L)))) (configurationTail_preserving n L)
  simp only [Function.comp_def] at he
  rw [he]
  have hv : volume (Set.univ : Set (Torus L))≠0 := Measure.measure_univ_ne_zero.mpr (NeZero.ne volume)
  rw [eLpNorm_smul_measure_of_ne_zero hv,smul_eq_mul,ENNReal.toReal_mul,Lp.norm_def]
  congr 2
  norm_num

def configurationTailCLM (n : ℕ) (L : Length) : ScalarL2 n L →L[ℂ] ScalarL2 (n+1) L :=
  (configurationTailLinear n L).mkContinuous
    (volume (Set.univ : Set (Torus L)) ^ (1 / (2:ℝ))).toReal
    (fun u ↦ (norm_configurationTailLp u).le)

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

def tailLift (n : ℕ) : LiftedConfiguration (n+1) →L[ℝ] LiftedConfiguration n :=
  .pi fun i ↦ .proj i.succ

lemma tailLift_direction_zero (n : ℕ) (j : Fin 3) :
    tailLift n (Pi.single 0 (Pi.single j 1))=0 := by
  ext i k
  simp [tailLift]

lemma tailLift_direction_succ (n : ℕ) (i : Fin n) (j : Fin 3) :
    tailLift n (Pi.single i.succ (Pi.single j 1))=Pi.single i (Pi.single j 1) := by
  ext k q
  by_cases h : k=i
  · subst k; simp [tailLift]
  · simp [tailLift,Pi.single_eq_of_ne h,Pi.single_eq_of_ne (fun h' ↦ h (Fin.succ_injective _ h'))]

lemma smooth_tail {n : ℕ} {L : Length} {f : Configuration n L → ℂ}
    (hf : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun X : LiftedConfiguration n ↦ f (project n L X))) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun X : LiftedConfiguration (n+1) ↦ f (Fin.tail (project (n+1) L X))) :=
  hf.comp (tailLift n).contDiff

lemma coordDerivative_tail_zero {n : ℕ} {L : Length} {f : Configuration n L → ℂ}
    (hf : Differentiable ℝ (fun X : LiftedConfiguration n ↦ f (project n L X))) (j : Fin 3) :
    coordDerivative (n+1) L (fun X ↦ f (Fin.tail X)) (0,j)=0 := by
  funext X
  have h := (hf (tailLift n (representative (n+1) L X))).hasFDerivAt.comp
    (representative (n+1) L X) (tailLift n).hasFDerivAt
  change (fderiv ℝ ((fun Y : LiftedConfiguration n ↦ f (project n L Y)) ∘ tailLift n)
    (representative (n+1) L X)) (Pi.single 0 (Pi.single j 1))=0
  rw [h.fderiv,ContinuousLinearMap.comp_apply,tailLift_direction_zero,map_zero]

lemma coordDerivative_tail_succ {n : ℕ} {L : Length} {f : Configuration n L → ℂ}
    (hf : Differentiable ℝ (fun X : LiftedConfiguration n ↦ f (project n L X)))
    (i : Fin n) (j : Fin 3) :
    coordDerivative (n+1) L (fun X ↦ f (Fin.tail X)) (i.succ,j)=
      fun X ↦ coordDerivative n L f (i,j) (Fin.tail X) := by
  funext X
  have h := (hf (tailLift n (representative (n+1) L X))).hasFDerivAt.comp
    (representative (n+1) L X) (tailLift n).hasFDerivAt
  change (fderiv ℝ ((fun Y : LiftedConfiguration n ↦ f (project n L Y)) ∘ tailLift n)
    (representative (n+1) L X)) (Pi.single i.succ (Pi.single j 1))=_
  rw [h.fderiv,ContinuousLinearMap.comp_apply,tailLift_direction_succ]
  rfl

lemma allowed_of_tail {n : ℕ} {L : Length} {a : ℝ} {X : Configuration (n+1) L}
    (htail : Fin.tail X∈allowed n L a)
    (hhead : ∀ i : Fin n, a<torusDistance L (X 0) (X i.succ)) :
    X∈allowed (n+1) L a := by
  intro i
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · intro j hij
    exact Fin.cases (fun h ↦ (lt_irrefl _ h).elim) (fun k _ ↦ hhead k) j hij
  · intro j hij
    exact Fin.cases (fun h ↦ (Fin.not_lt_zero _ h).elim)
      (fun l h ↦ htail k l (Fin.succ_lt_succ_iff.mp h)) j hij

def InsertionClearance {n : ℕ} {L : Length} (a : ℝ) (f : SmoothMultiplier (n+1) L) : Prop :=
  tsupport f.toFun ⊆ {X | ∀ i : Fin n, a<torusDistance L (X 0) (X i.succ)}

def SmoothTest.insert {n : ℕ} {L : Length} {a : ℝ} (g : SmoothTest n L a)
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f) : SmoothTest (n+1) L a where
  toFun := fun X ↦ f.toFun X * g.toFun (Fin.tail X)
  smooth := f.smooth.mul (smooth_tail g.smooth)
  compact := HasCompactSupport.of_compactSpace _
  support_allowed := by
    intro X hX
    have hf : X∈tsupport f.toFun := tsupport_mul_subset_left hX
    have hg : X∈tsupport (fun X : Configuration (n+1) L ↦ g.toFun (Fin.tail X)) :=
      tsupport_mul_subset_right hX
    have htail : Fin.tail X∈tsupport g.toFun := by
      exact (tsupport_comp_subset_preimage g.toFun
        (f := (Fin.tail : Configuration (n+1) L → Configuration n L))
        (continuous_pi fun i ↦ continuous_apply i.succ)) hg
    exact allowed_of_tail (g.support_allowed htail) (hc hf)
  memLp := (memLp_configurationTail g.memLp).mul f.memLp_top
  partial_memLp := by
    rintro ⟨i,j⟩
    rw [show (fun X ↦ f.toFun X*g.toFun (Fin.tail X))=f.toFun*(fun X ↦ g.toFun (Fin.tail X)) from rfl,
      coordDerivative_mul (f.smooth.differentiable (by simp)) ((smooth_tail g.smooth).differentiable (by simp))]
    apply MemLp.add
    · refine Fin.cases ?_ (fun k ↦ ?_) i
      · rw [coordDerivative_tail_zero (g.smooth.differentiable (by simp))]
        simp
      · rw [coordDerivative_tail_succ (g.smooth.differentiable (by simp))]
        exact (memLp_configurationTail (g.partial_memLp (k,j))).mul f.memLp_top
    · exact (f.partial_memLp_top (i,j)).mul (memLp_configurationTail g.memLp)

def insertionParentDerivative (n : ℕ) (L : Length) (p : Direction (n+1)) :
    Jet n L →L[ℂ] ScalarL2 n L :=
  Fin.cases 0 (fun i ↦ (ContinuousLinearMap.proj (i,p.2)).comp (.snd ℂ _ _)) p.1

def SmoothMultiplier.insertionScalar {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L) :
    ScalarL2 n L →L[ℂ] ScalarL2 (n+1) L :=
  f.onScalar.comp (configurationTailCLM n L)

def SmoothMultiplier.insertionJet {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L) :
    Jet n L →L[ℂ] Jet (n+1) L :=
  (f.insertionScalar.comp (.fst ℂ _ _)).prod (.pi fun p ↦
    f.insertionScalar.comp (insertionParentDerivative n L p) +
    ((L2Multiplier.clm _ (f.partial_memLp_top p)).comp (configurationTailCLM n L)).comp (.fst ℂ _ _))

end
end HardSphere

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TorusLiftBox
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

def torusLiftBox (L : Length) : Set (Fin 3 → ℝ) := Set.univ.pi (fun _ ↦ Set.Icc 0 L.val)

lemma isCompact_torusLiftBox (L : Length) : IsCompact (torusLiftBox L) := by
  simpa only [torusLiftBox] using
    (isCompact_univ_pi (fun _ : Fin 3 ↦ (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) L.val))))

lemma torusLiftBox_preserving (L : Length) :
    MeasurePreserving (fun X : Fin 3 → ℝ ↦ (fun j ↦ (X j : AddCircle L.val)))
      (volume.restrict (torusLiftBox L)) (volume : Measure (Torus L)) := by
  have hp := measurePreserving_pi (fun _ : Fin 3 ↦ volume.restrict (Set.Icc 0 L.val))
    (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val)))
    (f := fun _ X ↦ (X : AddCircle L.val)) (fun _ ↦ ?_)
  · change MeasurePreserving _ ((Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ))).restrict _)
        (Measure.pi (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val))))
    simpa only [torusLiftBox,Measure.restrict_pi_pi] using hp
  · simpa only [zero_add,restrict_Ioc_eq_restrict_Icc] using AddCircle.measurePreserving_mk L.val 0

lemma integral_torusLiftBox {L : Length} (f : Torus L → ℂ) (hf : Continuous f) :
    (∫ X in torusLiftBox L, f (fun j ↦ (X j : AddCircle L.val)))=∫ x : Torus L, f x := by
  have hp := torusLiftBox_preserving L
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable]

lemma SmoothMultiplier.smooth_fiberIntegral {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun Y : LiftedConfiguration n ↦
      ∫ x : Torus L, f.toFun (Fin.cons x (project n L Y))) := by
  let c : LiftedConfiguration n × (Fin 3 → ℝ) →L[ℝ] LiftedConfiguration (n+1) :=
    (ContinuousLinearMap.snd ℝ (LiftedConfiguration n) (Fin 3 → ℝ)).finCons
      (M := fun _ : Fin (n+1) ↦ Fin 3 → ℝ) (ContinuousLinearMap.fst ℝ _ _)
  have hc (z : LiftedConfiguration n × (Fin 3 → ℝ)) :
      project (n+1) L (c z)=Fin.cons (fun j ↦ (z.2 j : AddCircle L.val)) (project n L z.1) := by
    ext i j
    refine Fin.cases ?_ (fun k ↦ ?_) i <;> rfl
  have hs := CompactParameterIntegral.contDiff_integral (μ := (volume : Measure (Fin 3 → ℝ)))
    (f.smooth.comp c.contDiff) (isCompact_torusLiftBox L)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext Y
  simp only [Function.comp_def,hc]
  exact (integral_torusLiftBox _ ((continuous_of_continuous_lift f.smooth.continuous).comp
    ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
      (continuous_const : Continuous (fun _ : Torus L ↦ project n L Y))))).symm

def SmoothMultiplier.fiberMass {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (Y : Configuration n L) : ℝ := ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2

lemma SmoothMultiplier.smooth_fiberMass {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun Y : LiftedConfiguration n ↦ f.fiberMass (project n L Y)) := by
  have hs := Complex.reCLM.contDiff.comp (f.mul f).smooth_fiberIntegral
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext Y
  have he (X) : (f.mul f).toFun X=((‖f.toFun X‖^2:ℝ):ℂ) := by
    change f.toFun X*f.toFun X=_
    calc
      _ = f.toFun X*conj (f.toFun X) := by rw [hr]
      _ = _ := by rw [Complex.mul_conj,Complex.sq_norm]
  simp only [Function.comp_def,he,Complex.reCLM_apply,integral_complex_ofReal,Complex.ofReal_re,
    SmoothMultiplier.fiberMass]

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

def SmoothMultiplier.massRoot {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hp : ∀ Y, 0<f.fiberMass Y) : SmoothMultiplier n L :=
  .ofSmooth (fun Y ↦ (Real.sqrt (f.fiberMass Y) : ℂ))
    (Complex.ofRealCLM.contDiff.comp ((f.smooth_fiberMass hr).sqrt (fun _ ↦ (hp _).ne')))

def SmoothMultiplier.normalization {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hp : ∀ Y, 0<f.fiberMass Y) : SmoothMultiplier (n+1) L :=
  .ofSmooth (fun X ↦ f.toFun X/(Real.sqrt (f.fiberMass (Fin.tail X)) : ℂ))
    (by
      simp only [div_eq_mul_inv]
      exact f.smooth.mul ((smooth_tail (f.massRoot hr hp).smooth).inv (fun _ ↦
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp _)).ne')))

end
end HardSphere

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RawAngleLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open PeriodicCutoff
open scoped ComplexConjugate

def rawAngleLift (n : ℕ) (L : Length) (r : ℝ) (i : Fin n) (R : LiftedConfiguration (n+1)) : ℝ :=
  angleLift L.val r (R 0-R i.succ)

def rawCutoffReal (n : ℕ) (L : Length) (r : ℝ) (X : Configuration (n+1) L) : ℝ :=
  ∏ i : Fin n, Real.sin (angle L.val r (X 0) (X i.succ))

lemma rawAngleLift_smooth (n : ℕ) (L : Length) (r : ℝ) (i : Fin n) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (rawAngleLift n L r i) :=
  (angleLift_smooth L.val r).comp ((contDiff_apply ℝ (Fin 3 → ℝ) 0).sub
    (contDiff_apply ℝ (Fin 3 → ℝ) i.succ))

lemma angle_project (n : ℕ) (L : Length) (r : ℝ) (i : Fin n) (R : LiftedConfiguration (n+1)) :
    angle L.val r (project (n+1) L R 0) (project (n+1) L R i.succ)=rawAngleLift n L r i R := by
  change Real.pi/2*Real.smoothTransition ((pairQ L.val (fun j ↦ (R 0 j : AddCircle L.val))
    (fun j ↦ (R i.succ j : AddCircle L.val))-2*r^2)/(2*r^2))=_
  rw [pairQ_coe]
  rfl

lemma rawCutoffReal_smooth (n : ℕ) (L : Length) (r : ℝ) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun R : LiftedConfiguration (n+1) ↦
      rawCutoffReal n L r (project (n+1) L R)) := by
  simp only [rawCutoffReal,angle_project]
  exact contDiff_prod (fun i _ ↦ (rawAngleLift_smooth n L r i).sin)

def rawCutoff (n : ℕ) (L : Length) (r : ℝ) : SmoothMultiplier (n+1) L :=
  .ofSmooth (fun X ↦ (rawCutoffReal n L r X : ℂ))
    (Complex.ofRealCLM.contDiff.comp (rawCutoffReal_smooth n L r))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TestVector
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
section

variable {N : ℕ} {L : Length} {a : ℝ} {I : Type*} [Fintype I]

def testVector (F : I → SmoothTest N L a) (X : Configuration N L) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i ↦ (F i).toFun X)

lemma testVector_smooth (F : I → SmoothTest N L a) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun R : LiftedConfiguration N ↦ testVector F (project N L R)) :=
  (contDiff_piLp 2).mpr (fun i ↦ (F i).smooth)

def rmsTestFun (F : I → SmoothTest N L a) (ε : ℝ) (X : Configuration N L) : ℂ :=
  HilbertRegularization.regularize ε (testVector F X)

lemma rmsTest_smooth (F : I → SmoothTest N L a) {ε : ℝ} (hε : 0<ε) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun R : LiftedConfiguration N ↦ rmsTestFun F ε (project N L R)) :=
  (HilbertRegularization.smooth hε).comp (testVector_smooth F)

lemma rmsTest_support (F : I → SmoothTest N L a) {ε : ℝ} (hε : 0<ε) :
    tsupport (rmsTestFun F ε)⊆allowed N L a := by
  have hs : tsupport (rmsTestFun F ε)⊆⋃ i,tsupport (F i).toFun := by
    apply closure_minimal ?_ (isClosed_iUnion_of_finite (fun i ↦ isClosed_tsupport (F i).toFun))
    intro X hX
    by_contra hn
    have hz : testVector F X=0 := by
      ext i
      change (F i).toFun X=0
      exact image_eq_zero_of_notMem_tsupport (fun hi ↦ hn (Set.mem_iUnion.mpr ⟨i,hi⟩))
    exact hX (by change HilbertRegularization.regularize ε (testVector F X)=0; rw [hz,HilbertRegularization.zero hε.le])
  intro X hX
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hs hX)
  exact (F i).support_allowed hi

def SmoothTest.rms (F : I → SmoothTest N L a) {ε : ℝ} (hε : 0<ε) : SmoothTest N L a where
  toFun := rmsTestFun F ε
  smooth := rmsTest_smooth F hε
  compact := HasCompactSupport.of_compactSpace _
  support_allowed := rmsTest_support F hε
  memLp := (continuous_of_continuous_lift (rmsTest_smooth F hε).continuous).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  partial_memLp := fun p ↦ (continuous_coordDerivative (rmsTest_smooth F hε) p).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_HeadLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

def headLift (n : ℕ) : LiftedConfiguration (n+1) →L[ℝ] LiftedConfiguration 1 :=
  .pi fun _ ↦ .proj 0

lemma SmoothMultiplier.orbital_continuous {L : Length} (w : SmoothMultiplier 1 L) :
    Continuous w.orbital :=
  (continuous_of_continuous_lift w.smooth.continuous).comp (continuous_pi fun _ ↦ continuous_id)

def SmoothMultiplier.orbitalBound {L : Length} (w : SmoothMultiplier 1 L) : ℝ :=
  ‖(⟨w.orbital,w.orbital_continuous⟩ : C(Torus L,ℂ))‖^2

def SmoothMultiplier.orbitalEnergy {L : Length} (w : SmoothMultiplier 1 L) : ℝ :=
  ∑ j : Fin 3, ∫ x : Torus L, ‖coordDerivative 1 L w.toFun (0,j) (fun _ ↦ x)‖^2

def SmoothMultiplier.liftHead {L : Length} (w : SmoothMultiplier 1 L) (n : ℕ) :
    SmoothMultiplier (n+1) L :=
  .ofSmooth (fun X ↦ w.orbital (X 0)) (w.smooth.comp (headLift n).contDiff)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ScalarPartitionIms
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

def productPartition (n : ℕ) (L : Length) (a c : SmoothMultiplier 1 L) (σ : Fin n → Bool) :
    SmoothMultiplier n L :=
  SmoothMultiplier.finsetProd Finset.univ (fun i ↦ (cond (σ i) a c).liftLabel n i)

end
end HardSphere

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PartitionErrorIntegral
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter

noncomputable def selectedEnergy {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p]
    (u : Jet n L) : ℝ := ∑ i : {i // p i}, ∑ q : Fin 3, ‖u.2 (i.val,q)‖^2

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SelectedEnergyAddCompl
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Convolution NNReal

def spatialProject (L : Length) (x : SpatialLift) : Torus L := fun j ↦ (x j : AddCircle L.val)

lemma continuous_spatialProject (L : Length) : Continuous (spatialProject L) :=
  continuous_pi (fun j ↦ (AddCircle.continuous_mk' L.val).comp (continuous_apply j))

lemma spatialProject_sub (L : Length) (x y : SpatialLift) :
    spatialProject L (x-y)=spatialProject L x-spatialProject L y := by
  ext j
  exact QuotientAddGroup.mk_sub (AddSubgroup.zmultiples L.val) (x j) (y j)

def torusMollify (L : Length) (φ : ContDiffBump (0 : SpatialLift)) (f : Torus L → ℝ) (x : Torus L) : ℝ :=
  ∫ y : SpatialLift, φ.normed volume y*f (x-spatialProject L y)

lemma torusMollify_lift (L : Length) (φ : ContDiffBump (0 : SpatialLift)) (f : Torus L → ℝ) :
    (fun x : SpatialLift ↦ torusMollify L φ f (spatialProject L x))=
      φ.normed volume ⋆[lsmul ℝ ℝ,volume] (fun x ↦ f (spatialProject L x)) := by
  funext x
  simp only [torusMollify,convolution,lsmul_apply,smul_eq_mul,spatialProject_sub]

lemma torusMollify_smooth (L : Length) (φ : ContDiffBump (0 : SpatialLift))
    (f : Torus L → ℝ) (hf : Continuous f) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun x : SpatialLift ↦ torusMollify L φ f (spatialProject L x)) := by
  rw [torusMollify_lift]
  exact φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed
    (hf.comp (continuous_spatialProject L)).locallyIntegrable

def mollifiedSpatialMultiplier (L : Length) (φ : ContDiffBump (0 : SpatialLift))
    (f : Torus L → ℝ) (hf : Continuous f) : SmoothMultiplier 1 L :=
  SmoothMultiplier.ofSmooth (fun X ↦ (torusMollify L φ f (X 0) : ℂ))
    (Complex.ofRealCLM.contDiff.comp ((torusMollify_smooth L φ f hf).comp (contDiff_apply ℝ SpatialLift 0)))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_SafeMass
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.fiberMass_nonneg {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (Y : Configuration n L) : 0≤f.fiberMass Y :=
  integral_nonneg fun _ ↦ sq_nonneg _

def SmoothMultiplier.safeRoot {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) : SmoothMultiplier n L :=
  .ofSmooth (fun Y ↦ (Real.sqrt (safeMass (f.fiberMass Y)) : ℂ))
    (Complex.ofRealCLM.contDiff.comp ((safeMass_smooth.comp (f.smooth_fiberMass hr)).sqrt
      (fun _Y ↦ (safeMass_pos (f.fiberMass_nonneg _)).ne')))

def SmoothMultiplier.localNormalization {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) : SmoothMultiplier (n+1) L :=
  .ofSmooth (fun X ↦ f.toFun X/(Real.sqrt (safeMass (f.fiberMass (Fin.tail X))) : ℂ))
    (by
      simp only [div_eq_mul_inv]
      exact f.smooth.mul ((smooth_tail (f.safeRoot hr).smooth).inv (fun _ ↦
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (safeMass_pos (f.fiberMass_nonneg _))).ne')))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_Near
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.TightCutoff
open PeriodicCutoff MeasureTheory Set
noncomputable section

variable (L : ℝ) [hL : Fact (0<L)]

def near (r : ℝ) (x : ThreeTorus L) : Set (ThreeTorus L) :=
  {y | pairQ L y x≤(3/2)*r^2}

end
end HardSphere.TightCutoff

namespace HardSphere.TightCutoff
open PeriodicCutoff
variable (L : ℝ) [hL : Fact (0<L)]

def angleFactor (r : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  2*Real.pi/r^2*deriv Real.smoothTransition ((qLift L z-(5/4)*r^2)/((1/4)*r^2))

def anglePartial (r : ℝ) (z : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  angleFactor L r z*deriv (chordLift L) (z j)

end HardSphere.TightCutoff

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_RawAngleLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.TightCutoff
open PeriodicCutoff
open scoped ComplexConjugate

def rawAngleLift (n : ℕ) (L : Length) (r : ℝ) (i : Fin n) (R : LiftedConfiguration (n+1)) : ℝ :=
  angleLift L.val r (R 0-R i.succ)

def rawCutoffReal (n : ℕ) (L : Length) (r : ℝ) (X : Configuration (n+1) L) : ℝ :=
  ∏ i : Fin n, Real.sin (angle L.val r (X 0) (X i.succ))

lemma rawAngleLift_smooth (n : ℕ) (L : Length) (r : ℝ) (i : Fin n) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (rawAngleLift n L r i) :=
  (angleLift_smooth L.val r).comp ((contDiff_apply ℝ (Fin 3 → ℝ) 0).sub
    (contDiff_apply ℝ (Fin 3 → ℝ) i.succ))

lemma angle_project (n : ℕ) (L : Length) (r : ℝ) (i : Fin n) (R : LiftedConfiguration (n+1)) :
    angle L.val r (project (n+1) L R 0) (project (n+1) L R i.succ)=rawAngleLift n L r i R := by
  change Real.pi/2*Real.smoothTransition ((pairQ L.val (fun j ↦ (R 0 j : AddCircle L.val))
    (fun j ↦ (R i.succ j : AddCircle L.val))-(5/4)*r^2)/((1/4)*r^2))=_
  rw [pairQ_coe]
  rfl

lemma rawCutoffReal_smooth (n : ℕ) (L : Length) (r : ℝ) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun R : LiftedConfiguration (n+1) ↦
      rawCutoffReal n L r (project (n+1) L R)) := by
  simp only [rawCutoffReal,angle_project]
  exact contDiff_prod (fun i _ ↦ (rawAngleLift_smooth n L r i).sin)

def rawCutoff (n : ℕ) (L : Length) (r : ℝ) : SmoothMultiplier (n+1) L :=
  .ofSmooth (fun X ↦ (rawCutoffReal n L r X : ℂ))
    (Complex.ofRealCLM.contDiff.comp (rawCutoffReal_smooth n L r))

end HardSphere.TightCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_CloseLabels
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.TightCutoff
open PeriodicCutoff MeasureTheory Set Filter
open scoped ComplexConjugate

def closeLabels {n : ℕ} {L : Length} (r : ℝ) (w : SmoothMultiplier 1 L)
    (Y : Configuration n L) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i ↦ ∃ y∈tsupport w.orbital, torusDistance L y (Y i)≤2*r)

def orbitalCutoff {L : Length} (n : ℕ) (r : ℝ) (w : SmoothMultiplier 1 L) : SmoothMultiplier (n+1) L :=
  (w.liftHead n).mul (rawCutoff n L r)

end HardSphere.TightCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EuclideanTorus
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped NNReal ComplexConjugate

lemma spatialSiteDistance_lipschitz (L : Length) (A : Finset (Torus L)) :
    LipschitzWith spatialMetricConstant (spatialSiteDistance L A) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (Metric.lipschitz_infDist_pt (euclideanTorusPoint L '' (A:Set (Torus L)))).dist_le_mul
    (euclideanTorusPoint L x) (euclideanTorusPoint L y)
  have ht := (PiLp.lipschitzWith_toLp 2 (fun _ : Fin 3 ↦ AddCircle L.val)).dist_le_mul x y
  apply h.trans
  rw [NNReal.coe_one,one_mul]
  convert ht using 1 <;> rfl

def smoothSpatialDistance (L : Length) (A : Finset (Torus L)) : Torus L → ℝ :=
  torusMollify L spatialDistanceBump (spatialSiteDistance L A)

def spatialDistanceMultiplier (L : Length) (A : Finset (Torus L)) : SmoothMultiplier 1 L :=
  mollifiedSpatialMultiplier L spatialDistanceBump (spatialSiteDistance L A)
    (spatialSiteDistance_lipschitz L A).continuous

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

def spatialAngle (H t : ℝ) : ℝ := Real.pi/2*CellOrbital.profile 1 (t-H)
def spatialSine (H t : ℝ) : ℝ := Real.sin (spatialAngle H t)
def spatialCosine (H t : ℝ) : ℝ := Real.cos (spatialAngle H t)

lemma spatialAngle_smooth (H : ℝ) : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (spatialAngle H) :=
  contDiff_const.mul ((CellOrbital.profile_smooth 1).comp (contDiff_id.sub contDiff_const))
lemma spatialSine_smooth (H : ℝ) : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (spatialSine H) :=
  Real.contDiff_sin.comp (spatialAngle_smooth H)
lemma spatialCosine_smooth (H : ℝ) : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (spatialCosine H) :=
  Real.contDiff_cos.comp (spatialAngle_smooth H)

def spatialInside (L : Length) (A : Finset (Torus L)) (H : ℝ) : SmoothMultiplier 1 L :=
  (spatialDistanceMultiplier L A).realComp (spatialSine H) (spatialSine_smooth H)
def spatialOutside (L : Length) (A : Finset (Torus L)) (H : ℝ) : SmoothMultiplier 1 L :=
  (spatialDistanceMultiplier L A).realComp (spatialCosine H) (spatialCosine_smooth H)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CenteredCircleLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

def centeredCircleLift (L : Length) (x : AddCircle L.val) : ℝ :=
  let t := ((AddCircle.equivIco L.val 0) x).val
  t-(round (L.val⁻¹*t):ℝ)*L.val

def centeredTorusVector (L : Length) (x c : Torus L) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun q ↦ centeredCircleLift L (x q-c q))

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma nearestLabel_ne (L : Length) (X : ι→Torus L) (i : ι) : nearestLabel L X i≠i :=
  (Classical.choose_spec (nearestLabel_exists L X i)).1

lemma nearestParticleDistance_le (L : Length) (X : ι→Torus L) (i j : ι) (hji : j≠i) :
    nearestParticleDistance L X i≤torusDistance L (X i) (X j) :=
  (Classical.choose_spec (nearestLabel_exists L X i)).2 j hji

lemma nearestParticleDistance_inf (L : Length) (X : ι→Torus L) (i : ι) :
    nearestParticleDistance L X i=(Finset.univ.erase i).inf' (otherLabels_nonempty i)
      (fun j ↦ torusDistance L (X i) (X j)) := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro j hj
    exact nearestParticleDistance_le L X i j (Finset.mem_erase.mp hj).1
  · exact Finset.inf'_le _ (Finset.mem_erase.mpr ⟨nearestLabel_ne L X i,Finset.mem_univ _⟩)

lemma nearestParticleDistance_continuous (L : Length) (i : ι) :
    Continuous (fun X : ι→Torus L ↦ nearestParticleDistance L X i) := by
  simp_rw [nearestParticleDistance_inf]
  apply Continuous.finset_inf'_apply
  intro j _
  unfold torusDistance
  fun_prop

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_InjectiveNear
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

def closeAmplitude (L : Length) (s : ℝ) (v : Torus L) (X : ι→Torus L) (i : ι) : ℝ :=
  closeRamp (6-torusDistance L (X i) v)*closeRamp (2-nearestParticleDistance L X i/s)

def localCloseRoot (L : Length) (s : ℝ) (v : Torus L) (X : ι→Torus L) : ℝ :=
  ‖(WithLp.toLp 2 (closeAmplitude L s v X) : EuclideanSpace ℝ ι)‖

def localCloseSmoothCount (L : Length) (s : ℝ) (v : Torus L) (X : ι→Torus L) : ℝ :=
  ∑ i, closeAmplitude L s v X i^2

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Fourier_ArgumentAdd
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate

namespace HardSphere
open Wiener ProbabilityTheory
open scoped ComplexConjugate

def configurationCharacter (N : ℕ) (L : Length) (k : Direction N → ℤ) :
    C(Configuration N L, ℂ) where
  toFun X := ∏ p : Direction N, fourier (k p) (X p.1 p.2)
  continuous_toFun := by fun_prop

lemma configurationCharacter_add_argument (N : ℕ) (L : Length) (k : Direction N → ℤ)
    (X Y : Configuration N L) :
    configurationCharacter N L k (X+Y) =
      configurationCharacter N L k X * configurationCharacter N L k Y := by
  simp only [configurationCharacter, ContinuousMap.coe_mk, Pi.add_apply,
    FreeFourier.argument_add, Finset.prod_mul_distrib]

def fourierEnergy (N : ℕ) (L : Length) (k : Direction N → ℤ) : ℝ :=
  ∑ p : Direction N, (((2 : ℕ) : ℝ)*Real.pi*k p/L.val)^2

end HardSphere

namespace HardSphere
open scoped ComplexConjugate
open Submodule Algebra
lemma configurationCharacter_neg (N : ℕ) (L : Length) (k : Direction N → ℤ)
    (X : Configuration N L) :
    configurationCharacter N L (-k) X = conj (configurationCharacter N L k X) := by
  simp only [configurationCharacter, Pi.neg_apply, fourier_neg, ContinuousMap.coe_mk, map_prod]

def characterAlgebra (N : ℕ) (L : Length) : StarSubalgebra ℂ C(Configuration N L, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range (configurationCharacter N L))
  star_mem' := by
    change Algebra.adjoin ℂ (range (configurationCharacter N L)) ≤
      star (Algebra.adjoin ℂ (range (configurationCharacter N L)))
    refine adjoin_le ?_
    rintro _ ⟨k,rfl⟩
    refine subset_adjoin ⟨-k, ?_⟩
    ext X
    simp only [configurationCharacter_neg, starRingEnd_apply, ContinuousMap.star_apply]

section

attribute [local instance] scalarL2_addCommMonoid scalarL2_module

attribute [local instance] OAI.HardSphere.complexBoundedSMul
def characterL2 (N : ℕ) (L : Length) (k : Direction N → ℤ) : ScalarL2 N L :=
  DFunLike.coe (F := C(Configuration N L, ℂ) →L[ℂ] ScalarL2 N L)
    (β := fun _ ↦ ScalarL2 N L)
    (@ContinuousMap.toLp _ ℂ _ _ volume _ _ _ _ _ _ ℂ _ _ _ complexBoundedSMul)
    (configurationCharacter N L k)

end

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_FreeTransition
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open Wiener ProbabilityTheory
open scoped ComplexConjugate

def freeTransition (N : ℕ) (L : Length) (t : ℝ) : ScalarL2 N L →L[ℂ] ScalarL2 N L :=
  (endpointPull N L t 0).toContinuousLinearMap.adjoint ∘L
    (endpointPull N L t 1).toContinuousLinearMap

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_KilledObservable
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open Wiener
open scoped ComplexConjugate

def killedObservable (N : ℕ) (L : Length) (a : ℝ)
    (g : Configuration N L → ℂ) (ω : ConfigurationPath N L) : ℂ :=
  (staysAllowed N L a).indicator (fun ω ↦ g (ω 1)) ω

lemma killedObservable_measurable (N : ℕ) (L : Length) (a : ℝ)
    {g : Configuration N L → ℂ} (hg : Measurable g) :
    Measurable (killedObservable N L a g) :=
  (hg.comp (continuous_eval_const (1:Time)).measurable).indicator
    (staysAllowed_open N L a).measurableSet

lemma killedObservable_bound (N : ℕ) (L : Length) (a : ℝ)
    {g : Configuration N L → ℂ} {C : ℝ} (hC : 0≤C) (hg : ∀ X, ‖g X‖≤C)
    (ω : ConfigurationPath N L) : ‖killedObservable N L a g ω‖≤C := by
  by_cases ha : ω∈staysAllowed N L a
  · simpa only [killedObservable,Set.indicator_of_mem ha] using hg (ω 1)
  · simpa only [killedObservable,Set.indicator_of_notMem ha,norm_zero] using hC

def killedAverage (N : ℕ) (L : Length) (a t : ℝ)
    (g : Configuration N L → ℂ) (X : Configuration N L) : ℂ :=
  ∫ w, killedObservable N L a g (freeTrajectory N L t w X) ∂coordinateWiener N

lemma killedAverage_measurable (N : ℕ) (L : Length) (a t : ℝ)
    {g : Configuration N L → ℂ} (hg : Measurable g) :
    Measurable (killedAverage N L a t g) := by
  exact (((killedObservable_measurable N L a hg).comp
    (freeTrajectory_continuous N L t).measurable).stronglyMeasurable.integral_prod_left').measurable

lemma killedAverage_bound (N : ℕ) (L : Length) (a t : ℝ)
    {g : Configuration N L → ℂ} {C : ℝ} (hC : 0≤C) (hg : ∀ X, ‖g X‖≤C)
    (X : Configuration N L) : ‖killedAverage N L a t g X‖≤C := by
  simpa only [killedAverage,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
    norm_integral_le_of_norm_le_const (μ := coordinateWiener N)
      (Filter.Eventually.of_forall fun w ↦ killedObservable_bound N L a hC hg
        (freeTrajectory N L t w X))

lemma killedAverage_memLp (N : ℕ) (L : Length) (a t : ℝ)
    {g : Configuration N L → ℂ} (hg : Measurable g) {C : ℝ}
    (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) :
    MemLp (killedAverage N L a t g) 2 (volume : Measure (Configuration N L)) :=
  MemLp.of_bound (killedAverage_measurable N L a t hg).aestronglyMeasurable C
    (Filter.Eventually.of_forall (killedAverage_bound N L a t hC hgC))

def splitObservable (N : ℕ) (L : Length) (a : ℝ) (g : Configuration N L → ℂ)
    (p : ConfigurationPath N L × ConfigurationPath N L) : ℂ := by
  classical
  exact if p.1∈staysAllowed N L a then killedObservable N L a g p.2 else 0

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_HeatScalar
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

local instance scalarOperatorRealAlgebra (N : ℕ) (L : Length) :
    Algebra ℝ (ScalarL2 N L →L[ℂ] ScalarL2 N L) := Algebra.restrictScalars ℝ ℂ _

def formHeat (N : ℕ) (L : Length) (a t : ℝ) : ScalarL2 N L →L[ℂ] ScalarL2 N L :=
  cfc (p := IsSelfAdjoint) (heatScalar t) (formResolvent N L a)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Fourier_CharacterDerivativeFactor
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open scoped ComplexConjugate

lemma configurationCharacter_smooth (N : ℕ) (L : Length) (k : Direction N → ℤ) :
    configurationCharacter N L k ∈ smoothAlgebra N L := by
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun X : LiftedConfiguration N ↦ ∏ p : Direction N, fourier (k p) (X p.1 p.2 : AddCircle L.val))
  apply contDiff_prod
  intro p _
  simp_rw [fourier_coe_apply]
  exact Complex.contDiff_exp.comp
    ((((contDiff_const.mul contDiff_const).mul contDiff_const).mul contDiff_const).mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_apply_apply ℝ ℝ p.1 p.2)) |>.div_const _)

lemma configurationCharacter_single_argument (N : ℕ) (L : Length) (k : Direction N → ℤ)
    (p : Direction N) (z : AddCircle L.val) :
    configurationCharacter N L k (Pi.single p.1 (Pi.single p.2 z))=fourier (k p) z := by
  unfold configurationCharacter
  simp only [ContinuousMap.coe_mk]
  rw [Finset.prod_eq_single p]
  · simp
  · intro q _ hq
    have hh : q.1≠p.1 ∨ q.2≠p.2 := by
      by_contra hh
      push Not at hh
      exact hq (Prod.ext hh.1 hh.2)
    rcases hh with h | h
    · simp [Pi.single_eq_of_ne h]
    · by_cases h' : q.1=p.1 <;> simp [h',Pi.single_eq_of_ne h]
  · simp

lemma configurationCharacter_coordinateLine (N : ℕ) (L : Length) (k : Direction N → ℤ)
    (X : Configuration N L) (p : Direction N) (z : AddCircle L.val) :
    configurationCharacter N L k (coordinateLine X p z)=
      configurationCharacter N L k X * fourier (k p) z := by
  rw [coordinateLine,configurationCharacter_add_argument,configurationCharacter_single_argument]

def characterDerivativeFactor (L : Length) (n : ℤ) : ℂ :=
  ((2 : ℕ) : ℂ)*Real.pi*Complex.I*n/L.val

lemma configurationCharacter_partial (N : ℕ) (L : Length) (k : Direction N → ℤ)
    (p : Direction N) (X : Configuration N L) :
    coordDerivative N L (configurationCharacter N L k) p X =
      characterDerivativeFactor L (k p)*configurationCharacter N L k X := by
  have h := hasDerivAt_coordinateLine
    ((show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Z : LiftedConfiguration N ↦ configurationCharacter N L k (project N L Z)) from configurationCharacter_smooth N L k).differentiable (by simp)) X p 0
  have g := (hasDerivAt_fourier L.val (k p) 0).const_mul (configurationCharacter N L k X)
  simp_rw [configurationCharacter_coordinateLine] at h
  have heq := h.unique g
  simpa [coordinateLine,characterDerivativeFactor,mul_comm] using heq

lemma allowed_of_neg (N : ℕ) (L : Length) {a : ℝ} (ha : a<0) : allowed N L a=Set.univ := by
  ext X
  simp only [Set.mem_univ,iff_true]
  intro i j _
  exact ha.trans_le (Real.sqrt_nonneg _)

def characterTest (N : ℕ) (L : Length) (a : ℝ) (ha : a<0) (k : Direction N → ℤ) :
    SmoothTest N L a where
  toFun := configurationCharacter N L k
  smooth := configurationCharacter_smooth N L k
  compact := HasCompactSupport.of_compactSpace _
  support_allowed := by rw [allowed_of_neg N L ha]; exact Set.subset_univ _
  memLp := (configurationCharacter N L k).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  partial_memLp p := by
    have heq : coordDerivative N L (configurationCharacter N L k) p =
        fun X ↦ characterDerivativeFactor L (k p)*configurationCharacter N L k X :=
      funext (configurationCharacter_partial N L k p)
    rw [heq]
    exact ((configurationCharacter N L k).continuous.const_mul _).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_AllowedProjection
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open Wiener ContinuousLinearMap
open scoped ComplexConjugate

def allowedProjection (N : ℕ) (L : Length) (a : ℝ) : ScalarL2 N L→L[ℂ] ScalarL2 N L :=
  L2Multiplier.clm ((allowed N L a).indicator (fun _ ↦ (1:ℂ)))
    ((memLp_top_const (1:ℂ)).indicator (isOpen_allowed N L a).measurableSet)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PartialAlgebra
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology

lemma smoothPartial_smooth {N : ℕ} {L : Length} (f : smoothAlgebra N L) (p : Direction N) :
    smoothPartial f p∈smoothAlgebra N L := by
  change ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
    (fun X : LiftedConfiguration N ↦ coordDerivative N L f.val p (project N L X))
  simp_rw [coordDerivative_project]
  have hf : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun X : LiftedConfiguration N ↦ f.val (project N L X)) := f.property
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

def partialAlgebra {N : ℕ} {L : Length} (f : smoothAlgebra N L) (p : Direction N) :
    smoothAlgebra N L := ⟨smoothPartial f p,smoothPartial_smooth f p⟩

def smoothLaplacian {N : ℕ} {L : Length} (f : smoothAlgebra N L) : ScalarL2 N L :=
  -∑ p : Direction N, ContinuousMap.toLp 2 volume ℂ (smoothPartial (partialAlgebra f p) p)

def SmoothTest.asSmooth {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    smoothAlgebra N L := ⟨⟨f.toFun,f.continuous⟩,f.smooth⟩

def SmoothTest.freeTest {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    SmoothTest N L (-1) where
  toFun := f.toFun
  smooth := f.smooth
  compact := f.compact
  support_allowed := by rw [allowed_of_neg N L (by norm_num : (-1:ℝ)<0)]; exact subset_univ _
  memLp := f.memLp
  partial_memLp := f.partial_memLp

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_KilledLaplace
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology

def killedLaplace (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) : ScalarL2 N L :=
  semigroupLaplace (killedTransition N L a) f

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_BufferedAllowed
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology

def bufferedAllowed (N : ℕ) (L : Length) (b : ℝ) : Set (Configuration N L) :=
  {X | ∀ i j : Fin N, i<j → b≤torusDistance L (X i) (X j)}

end HardSphere

open ProbabilityTheory

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_Moment8
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.Wiener

def normMultiplier : ℝ := 1 + ∑' n : ℕ, amplitude n * (4/3:ℝ)^n

end HardSphere.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_PathTailConstant
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open Wiener

def pathTailConstant (N : ℕ) : ℝ :=
  ((Fintype.card (Direction N) : ℝ≥0∞) *
    ((1+(1-(2:ℝ≥0∞)*(4/3)⁻¹^8)⁻¹)*moment8)).toReal

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_FieldApply
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace HardSphere

namespace SmoothContraction
variable (f : SmoothContraction)

lemma coordDerivative_comp {N : ℕ} {L : Length} {a : ℝ}
    (g : SmoothTest N L a) (p : Direction N) :
    coordDerivative N L (f.toFun ∘ g.toFun) p = fun X ↦
      fderiv ℝ f.toFun (g.toFun X) (coordDerivative N L g.toFun p X) := by
  funext X
  unfold coordDerivative
  rw [show (fun Y : LiftedConfiguration N ↦ (f.toFun ∘ g.toFun) (project N L Y)) =
    f.toFun ∘ (fun Y ↦ g.toFun (project N L Y)) from rfl]
  rw [fderiv_comp (representative N L X)
    (f.smooth.differentiable (by simp)).differentiableAt
    (g.smooth.differentiable (by simp)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, project_representative]

def composeTest {N : ℕ} {L : Length} {a : ℝ}
    (g : SmoothTest N L a) : SmoothTest N L a where
  toFun := f.toFun ∘ g.toFun
  smooth := f.smooth.comp g.smooth
  compact := g.compact.comp_left f.zero
  support_allowed := (tsupport_comp_subset f.zero g.toFun).trans g.support_allowed
  memLp := f.lipschitz.comp_memLp f.zero g.memLp
  partial_memLp := by
    intro p
    rw [f.coordDerivative_comp g p]
    have hm := f.derivative_continuous.comp_aestronglyMeasurable g.memLp.aestronglyMeasurable
    apply (g.partial_memLp p).of_le
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hm.prodMk (g.partial_memLp p).aestronglyMeasurable))
    exact Eventually.of_forall fun X ↦
      (fderiv ℝ f.toFun (g.toFun X)).le_opNorm _ |>.trans
        (by nlinarith [f.derivative_le (g.toFun X),
          norm_nonneg (coordDerivative N L g.toFun p X)])

def onScalar {N : ℕ} {L : Length} (u : ScalarL2 N L) : ScalarL2 N L :=
  f.lipschitz.compLp f.zero u

def onPartial {N : ℕ} {L : Length} (u v : ScalarL2 N L) : ScalarL2 N L :=
  L2Contraction.fieldApply (fun X ↦ fderiv ℝ f.toFun (u X))
    (L2Contraction.coeff_meas _ f.derivative_continuous u)
    (Eventually.of_forall (fun X ↦ f.derivative_le (u X))) v

def onJet {N : ℕ} {L : Length} (u : Jet N L) : Jet N L :=
  (f.onScalar u.1, fun p ↦ f.onPartial u.1 (u.2 p))

end SmoothContraction
end HardSphere

open scoped RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_Regularize
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace

namespace HardSphere
open ComplexRegularization

def regularization (ε : ℝ) (hε : 0 < ε) : SmoothContraction where
  toFun := regularize ε
  smooth := smooth hε
  zero := zero hε.le
  derivative_le z := by rw [fderiv_eq hε]; exact differential_le ε z

def modulusScalar {N : ℕ} {L : Length} (u : ScalarL2 N L) : ScalarL2 N L :=
  modulus_lipschitz.compLp (by simp) u

lemma modulusCoefficient_meas {N : ℕ} {L : Length} (u : ScalarL2 N L) :
    AEStronglyMeasurable (fun X ↦ differential 0 (u X)) volume := by
  apply aestronglyMeasurable_of_tendsto_ae atTop (f := fun n X ↦
    differential (regularizationScale n) (u X))
  · intro n
    have he : differential (regularizationScale n) =
        fderiv ℝ (regularize (regularizationScale n)) :=
      funext fun z ↦ (fderiv_eq (regularizationScale_pos n) z).symm
    rw [he]
    exact ((smooth (regularizationScale_pos n)).continuous_fderiv (by simp)).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable u)
  · exact Eventually.of_forall fun X ↦ tendsto_differential (u X) tendsto_regularizationScale

def modulusPartial {N : ℕ} {L : Length} (u v : ScalarL2 N L) : ScalarL2 N L :=
  L2Contraction.fieldApply (fun X ↦ differential 0 (u X)) (modulusCoefficient_meas u)
    (Eventually.of_forall fun X ↦ differential_le 0 (u X)) v

def modulusJet {N : ℕ} {L : Length} (u : Jet N L) : Jet N L :=
  (modulusScalar u.1, fun p ↦ modulusPartial u.1 (u.2 p))

end HardSphere

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PointFin
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

noncomputable def cubeParameter (n : ℕ) (L : Length) (X : Fin n → Point) : Configuration n L :=
  project n L (configurationFin n X)

lemma cubeParameter_preserving (n : ℕ) (L : Length) :
    MeasurePreserving (cubeParameter n L)
      (Measure.pi (fun _ : Fin n ↦ volume.restrict (cube 0 L.val))) volume := by
  have hp := measurePreserving_pi (fun _ : Fin 3 ↦ (volume : Measure ℝ).restrict (Icc 0 L.val))
    (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val)))
    (f := fun _ x ↦ (x : AddCircle L.val)) (fun _ ↦ by
      simpa only [zero_add,restrict_Ioc_eq_restrict_Icc] using AddCircle.measurePreserving_mk L.val 0)
  have hq := measurePreserving_pi _ _ (fun _ : Fin n ↦ hp)
  have hs := configurationFin_preserving n 0 L.val
  simp only [zero_add] at hs
  exact hq.comp hs

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GroundPositionLaw
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

def groundPositionLaw (N : ℕ) (L : Length) (u : Jet N L) : Measure (Configuration N L) :=
  volume.withDensity (fun X ↦ ENNReal.ofReal (‖u.1 X‖^2))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GroundPathWeight
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace HardSphere
open MeasureTheory Wiener Set Filter
open scoped ComplexConjugate
noncomputable section
variable {N : ℕ} {L : Length} {a t : ℝ}

def groundPathWeight (u : Jet N L) (t : ℝ) (ω : ConfigurationPath N L) : ℝ :=
  Real.exp (t*energy u)*(‖u.1 (ω 0)‖*‖u.1 (ω 1)‖)

def groundPathLaw (N : ℕ) (L : Length) (a t : ℝ) (u : Jet N L) :
    Measure (ConfigurationPath N L) :=
  (killedPathLaw N L a t).withDensity (fun ω ↦ ENNReal.ofReal (groundPathWeight u t ω))

end
end HardSphere

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_JoinConfiguration
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Wiener.instIsProbabilityMeasureContinuousMapElemRealTimeBridgeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace HardSphere
open MeasureTheory Wiener Set Filter
noncomputable section

def directionSumEquiv (m n : ℕ) : Direction m ⊕ Direction n ≃ Direction (m+n) :=
  (Equiv.sumProdDistrib (Fin m) (Fin n) (Fin 3)).symm.trans
    ((finSumFinEquiv (m:=m) (n:=n)).prodCongr (Equiv.refl (Fin 3)))

def joinCoordinatePaths (m n : ℕ) (p : CoordinatePaths m × CoordinatePaths n) : CoordinatePaths (m+n) :=
  fun d ↦ Sum.elim p.1 p.2 ((directionSumEquiv m n).symm d)

end
end HardSphere

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SliceNormSq
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace HardSphere
open MeasureTheory Wiener Set Filter
noncomputable section

def sliceNormSq {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) (y : Configuration m L) : ℝ :=
  ∫ x : Configuration n L, ‖u (joinConfiguration m n L (y,x))‖^2 ∂volume

end
end HardSphere

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_FreePathLawFiniteDeletion
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace HardSphere
open MeasureTheory Wiener Set Filter
noncomputable section

instance freePathLaw_finite_deletion (N : ℕ) (L : Length) (t : ℝ) :
    IsFiniteMeasure (freePathLaw N L t) := by unfold freePathLaw; infer_instance
instance killedPathLaw_finite_deletion (N : ℕ) (L : Length) (a t : ℝ) :
    IsFiniteMeasure (killedPathLaw N L a t) := by unfold killedPathLaw; infer_instance

end
end HardSphere

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FreePathExpectation
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace HardSphere
open MeasureTheory Wiener Set Filter
noncomputable section

def freePathExpectation {m : ℕ} {L : Length} (t : ℝ)
    (h : ConfigurationPath m L → ℝ≥0∞) (X : Configuration m L) : ℝ≥0∞ :=
  ∫⁻ w : CoordinatePaths m, h (freeTrajectory m L t w X) ∂coordinateWiener m

end
end HardSphere

end
end
end

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

lemma onePathAt_continuous {n : ℕ} {L : Length} (i : Fin n) :
    Continuous (onePathAt (L:=L) i) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath n L × Time ↦ fun _ : Fin 1 ↦ p.1 p.2 i)
  fun_prop

def oneFreeExpectation {L : Length} (t : ℝ) (h : ConfigurationPath 1 L → ℝ≥0∞)
    (y : Torus L) : ℝ≥0∞ := freePathExpectation t h (oneConfiguration y)

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_WienerGaussian
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.coordinateWiener_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def dualCoefficient (L : C(Time,ℝ) →L[ℝ] ℝ) (n : ℕ) : PartialIndex n → ℝ
  | .inl _ => L linearPath
  | .inr ⟨m,k⟩ => amplitude m * L (tentMap m k)

end HardSphere.Wiener

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RadiusLaw
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ProbabilityTheory

def spatialEnergyError (L : Length) (A : Finset (Torus L)) (H : ℝ) (x : Torus L) : ℝ :=
  ∑ j : Fin 3, (‖coordDerivative 1 L (spatialInside L A H).toFun (0,j) (fun _ ↦ x)‖^2+
    ‖coordDerivative 1 L (spatialOutside L A H).toFun (0,j) (fun _ ↦ x)‖^2)

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter

def weightedSiteCount {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) : ℝ :=
  if A.Nonempty then ∑ i : Fin n, Real.exp (-spatialSiteDistance L A (X i)) else 0

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SpatialPartitionEnergy
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ENNReal

def spatialPartitionEnergy {n : ℕ} (L : Length) (A : Finset (Torus L)) (H : ℝ) (u : Jet n L) : ℝ :=
  ∑ σ : Fin n → Bool, selectedEnergy (fun i ↦ σ i=true)
    ((productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).onJet u)

end HardSphere

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CubeCell
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

noncomputable def unitSectorMeasure (n K : ℕ) (σ : Fin n → CubeCell K) : Measure (Fin n → Point) :=
  Measure.pi (fun i ↦ volume.restrict (cube (subcubeBase 0 1 (σ i)) 1))

lemma unitSectorMeasure_le {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (σ : Fin n → CubeCell K) :
    unitSectorMeasure n K σ≤Measure.pi (fun _ : Fin n ↦ volume.restrict (cube 0 L.val)) := by
  rw [hL,← mul_one (K:ℝ),cube_configuration_subdivision 0 (by norm_num : (0:ℝ)≤1)]
  exact Measure.le_sum _ σ

noncomputable def unitSectorRestriction {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (σ : Fin n → CubeCell K) : ScalarL2 n L →L[ℝ] Lp ℂ 2 (unitSectorMeasure n K σ) :=
  (Lp.LpToLpOfMeasureLeSMul (c := (1:ℝ≥0∞)) (by norm_num)
    (show unitSectorMeasure n K σ≤1 • Measure.pi (fun _ : Fin n ↦ volume.restrict (cube 0 L.val)) by
      simpa only [one_smul] using unitSectorMeasure_le hL σ)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (cubeParameter n L) (cubeParameter_preserving n L)).toContinuousLinearMap

end HardSphere

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_HalfShiftCover
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open Set Function MeasureTheory
open scoped ENNReal

namespace HardSphere
open SphericalCoordinates
open scoped BigOperators
lemma cubeParameter_preserving_base (n : ℕ) (L : Length) (b : Point) :
    MeasurePreserving (cubeParameter n L)
      (Measure.pi (fun _ : Fin n ↦ volume.restrict (cube b L.val))) volume := by
  have hp := measurePreserving_pi (fun q : Fin 3 ↦ (volume : Measure ℝ).restrict (Icc (pointFin b q) (pointFin b q+L.val)))
    (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val)))
    (f := fun _ x ↦ (x : AddCircle L.val)) (fun q ↦ by
      simpa only [restrict_Ioc_eq_restrict_Icc] using AddCircle.measurePreserving_mk L.val (pointFin b q))
  exact (measurePreserving_pi _ _ (fun _ : Fin n ↦ hp)).comp (configurationFin_preserving_base n b L.val)

noncomputable def gridSectorMeasure (n j : ℕ) (b : Point) (l : ℝ) (σ : Fin n → CubeCell j) : Measure (Fin n → Point) :=
  Measure.pi (fun i ↦ volume.restrict (cube (subcubeBase b l (σ i)) l))

lemma gridSectorMeasure_le {n j : ℕ} {L : Length} {l : ℝ} (hl : 0≤l) (hL : L.val=(j:ℝ)*l) (b : Point) (σ : Fin n → CubeCell j) :
    gridSectorMeasure n j b l σ≤Measure.pi (fun _ : Fin n ↦ volume.restrict (cube b L.val)) := by
  rw [hL,cube_configuration_subdivision b hl]
  exact Measure.le_sum _ σ

noncomputable def gridSectorRestriction {n j : ℕ} {L : Length} {l : ℝ} (hl : 0≤l) (hL : L.val=(j:ℝ)*l)
    (b : Point) (σ : Fin n → CubeCell j) : ScalarL2 n L →L[ℝ] Lp ℂ 2 (gridSectorMeasure n j b l σ) :=
  (Lp.LpToLpOfMeasureLeSMul (c := (1:ℝ≥0∞)) (by norm_num)
    (show gridSectorMeasure n j b l σ≤1 • Measure.pi (fun _ : Fin n ↦ volume.restrict (cube b L.val)) by
      simpa only [one_smul] using gridSectorMeasure_le hl hL b σ)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (cubeParameter n L) (cubeParameter_preserving_base n L b)).toContinuousLinearMap

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SelectedUnitCellPenalty
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

noncomputable def selectedUnitCellPenalty {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (a : ℝ) (u : ScalarL2 n L) : ℝ :=
  ∑ σ : Fin n → CubeCell K,
    (∑ v : CubeCell K,1/(64*Real.sqrt 3)*a*(Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)*
      ((Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)-1))*‖unitSectorRestriction hL σ u‖^2

noncomputable def unitSite {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (x : Torus L) : CubeCell K :=
  (unitIndex hL (x 0),unitIndex hL (x 1),unitIndex hL (x 2))

noncomputable def unitOccupation {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (X : Configuration n L) : ℕ :=
  Fintype.card {i : {i // p i} // unitSite hL (X i.val)=v}

noncomputable def occupationWeight {n K : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (a : ℝ) (σ : Fin n → CubeCell K) : ℝ :=
  ∑ v : CubeCell K,1/(64*Real.sqrt 3)*a*(Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)*
      ((Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)-1)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GridActivePenalty
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open Set Function MeasureTheory
open scoped ENNReal
namespace HardSphere
open SphericalCoordinates
open scoped BigOperators
noncomputable def gridActivePenalty {n j : ℕ} {L : Length} {l : ℝ}
    (hl : 0≤l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p]
    (u : ScalarL2 n L) : ℝ :=
  ∑ σ : Fin n → CubeCell j, ((activeLabels (fun i : {i // p i} ↦ σ i.val)).card:ℝ)*
    ‖gridSectorRestriction hl hL b σ u‖^2

noncomputable def gridSite {j : ℕ} [NeZero j] {L : Length} {l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (b : Point) (x : Torus L) : CubeCell j :=
  ((ZMod.finEquiv j).symm (GridGeometry.index hl hL b.1 (x 0)),
    (ZMod.finEquiv j).symm (GridGeometry.index hl hL b.2.1 (x 1)),
    (ZMod.finEquiv j).symm (GridGeometry.index hl hL b.2.2 (x 2)))

noncomputable def gridActiveCount {n j : ℕ} [NeZero j] {L : Length} {l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p]
    (X : Configuration n L) : ℕ :=
  (activeLabels (fun i : {i // p i} ↦ gridSite hl hL b (X i.val))).card

noncomputable def nearLabels {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p]
    (s : ℝ) (X : Configuration n L) : Finset {i // p i} := by
  classical
  exact Finset.univ.filter (fun i ↦ ∃ k : {i // p i}, k≠i ∧ torusDistance L (X k.val) (X i.val)≤2*s)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LocalizedNearLabels
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal

def localizedNearLabels {n : ℕ} (L : Length) (A : Finset (Torus L)) (s : ℝ)
    (X : Configuration n L) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i ↦ A.Nonempty ∧ spatialSiteDistance L A (X i)≤6 ∧
    ∃ k : Fin n, k≠i ∧ torusDistance L (X k) (X i)≤2*s)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SqTwiceSqAbs
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter

def euclideanProject {ι : Type*} (L : Length) (x : EuclideanConfiguration ι) : ι→Torus L :=
  fun i q ↦ (x (i,q) : AddCircle L.val)

lemma euclideanProject_continuous {ι : Type*} (L : Length) : Continuous (euclideanProject (ι:=ι) L) :=
  continuous_pi (fun i ↦ continuous_pi (fun q ↦
    (AddCircle.continuous_mk' L.val).comp (PiLp.continuous_apply 2 (fun _ : ι×Fin 3 ↦ ℝ) (i,q))))

lemma euclideanProject_sub {ι : Type*} (L : Length) (x y : EuclideanConfiguration ι) :
    euclideanProject L (x-y)=euclideanProject L x-euclideanProject L y := by
  ext i q
  exact QuotientAddGroup.mk_sub (AddSubgroup.zmultiples L.val) (x (i,q)) (y (i,q))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma closeAmplitude_continuous (L : Length) (s : ℝ) (v : Torus L) (i : ι) :
    Continuous (fun X : ι→Torus L ↦ closeAmplitude L s v X i) := by
  unfold closeAmplitude
  apply Continuous.mul
  · apply closeRamp_lipschitz.continuous.comp
    apply continuous_const.sub
    unfold torusDistance
    fun_prop
  · exact closeRamp_lipschitz.continuous.comp
      (continuous_const.sub ((nearestParticleDistance_continuous L i).div_const s))

lemma localCloseRoot_continuous (L : Length) (s : ℝ) (v : Torus L) :
    Continuous (localCloseRoot (ι:=ι) L s v) :=
  ((PiLp.continuous_toLp 2 (fun _ : ι ↦ ℝ)).comp
    (continuous_pi (fun i ↦ closeAmplitude_continuous L s v i))).norm

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LocalCloseLabels
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Convolution NNReal

variable {ι : Type*} [Fintype ι]

def configurationMollify (L : Length) (φ : ContDiffBump (0 : EuclideanConfiguration ι))
    (f : (ι→Torus L)→ℝ) (X : ι→Torus L) : ℝ :=
  ∫ y : EuclideanConfiguration ι, φ.normed volume y*f (X-euclideanProject L y)

lemma configurationMollify_lift (L : Length) (φ : ContDiffBump (0 : EuclideanConfiguration ι))
    (f : (ι→Torus L)→ℝ) :
    (fun x : EuclideanConfiguration ι ↦ configurationMollify L φ f (euclideanProject L x))=
      φ.normed volume ⋆[lsmul ℝ ℝ,volume] (fun x ↦ f (euclideanProject L x)) := by
  funext x
  simp only [configurationMollify,convolution,lsmul_apply,smul_eq_mul,euclideanProject_sub]

lemma configurationMollify_smooth (L : Length) (φ : ContDiffBump (0 : EuclideanConfiguration ι))
    (f : (ι→Torus L)→ℝ) (hf : Continuous f) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun x : EuclideanConfiguration ι ↦ configurationMollify L φ f (euclideanProject L x)) := by
  rw [configurationMollify_lift]
  exact φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed
    (hf.comp (euclideanProject_continuous L)).locallyIntegrable

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_BadGraph
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def candidateSets (G : SimpleGraph V) : Finset (Finset V) :=
  Finset.univ.filter (fun F ↦ F.Nonempty ∧
    ∀ x∈F, ∀ y∈F, (badGraph G F).Reachable x y)

def frontierHead (s : ExploreState V) (h : s.2.Nonempty) : V := h.choose

def exploreNext (s : ExploreState V) (A : Finset V) : ExploreState V :=
  if h : s.2.Nonempty then
    let x := frontierHead s h
    (insert x s.1, (s.2 ∪ A) \ insert x s.1)
  else s

def exploreStep (G : SimpleGraph V) (F : Finset V) (s : ExploreState V) : ExploreState V :=
  if h : s.2.Nonempty then exploreNext s ((G.neighborFinset (frontierHead s h)) ∩ F)
  else s

def exploration (G : SimpleGraph V) (F : Finset V) (r : V) : ℕ → ExploreState V
  | 0 => (∅,{r})
  | n+1 => exploreStep G F (exploration G F r n)

def ExploreInvariant (G : SimpleGraph V) (F : Finset V) (r : V) (s : ExploreState V) : Prop :=
  s.1 ⊆ F ∧ s.2 ⊆ F ∧ Disjoint s.1 s.2 ∧ r∈s.1∪s.2 ∧
    ∀ x∈s.1, ∀ y∈F, G.Adj x y → y∈s.1∪s.2

def possibleSteps (G : SimpleGraph V) (s : ExploreState V) : Finset (ExploreState V) :=
  if h : s.2.Nonempty then
    (G.neighborFinset (frontierHead s h)).powerset.image (exploreNext s)
  else {s}

def possibleStates (G : SimpleGraph V) (r : V) : ℕ → Finset (ExploreState V)
  | 0 => {(∅,{r})}
  | n+1 => (possibleStates G r n).biUnion (possibleSteps G)

end HardSphere.Lattice
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_Vertex
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

noncomputable section
open scoped BigOperators Classical
namespace HardSphere.Lattice

variable {A : Type*} [AddCommGroup A]

def coordinateBox (C : Finset Vertex) : Set Vertex :=
  {x | ∀ i, (∃ c∈C, c i≤x i) ∧ (∃ c∈C, x i ≤ c i)}

def coordinateRay (x : Vertex) (i : Fin 3) (d : ℤ) (n : ℕ) : Vertex :=
  fun j ↦ if j=i then x j+d*(n:ℤ) else x j

end HardSphere.Lattice
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_StarGraph
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice

def starGraph : SimpleGraph Vertex where
  Adj := starStep
  symm := ⟨fun _ _ ↦ starStep_symm⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

def restrictedStarGraph (D : Set Vertex) : SimpleGraph Vertex where
  Adj x y := x ∈ D ∧ y ∈ D ∧ starStep x y
  symm := ⟨fun _ _ h ↦ ⟨h.2.1, h.1, starStep_symm h.2.2⟩⟩
  loopless := ⟨fun _ h ↦ h.2.2.1 rfl⟩

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_AnimalFamily
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def animalFamily (G : SimpleGraph V) (m : ℕ) : Finset (Finset V) :=
  Finset.univ.biUnion (fun r : V ↦ rootedAnimals G r m)

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_MeshEvents
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

def meshEvent {L : Length} (m : ℕ) (E : Set (ConfigurationPath 1 L)) :=
  {ω : ConfigurationPath 1 L | ∃ j : Fin m, meshSegment j ω ∈ E}

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits BathSlice
attribute [local irreducible] torusDistance freeTrajectory

def noiseSize (w : CoordinatePaths 1) : ℝ := ∑ j : Fin 3, ‖w (0,j)‖

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_CubicMoment
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

def cubicMean : ℝ := ∫w : CoordinatePaths 1,(1+12*noiseSize w)^3 ∂coordinateWiener 1

def cappedWeight {L : Length} (r B : ℝ) (ω : ConfigurationPath 1 L) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (min (cubicCost r ω) B/B))

def meanCost : ℝ := (Real.exp 1-1)*cubicMean

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

def capSum {L : Length} (m : ℕ) (r B : ℝ) (ω : ConfigurationPath 1 L) : ℝ :=
  ∑j : Fin m, min (cubicCost r (meshSegment j ω)) B

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_PathLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

def IsPathLift {L : Length} (ω : ConfigurationPath 1 L) (ζ : EuclideanPath) : Prop :=
  ∀ j s, (ζ j s : AddCircle L.val)=ω s 0 j

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_Allocation
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Sampling
variable {I : Type*} [Fintype I] [DecidableEq I]

instance allocationFintype (m : ℕ) : Fintype (Allocation m I) := inferInstanceAs (Fintype (Option (Fin m↪I)))

def allocationPMF (E : Finset I) (m : ℕ) : PMF (Allocation m I) := by
  classical
  by_cases h : m≤E.card
  · haveI : Nonempty (Fin m↪E) := Function.Embedding.nonempty_of_card_le (by simpa using h)
    exact (PMF.uniformOfFintype (Fin m↪E)).map (fun f ↦ some (f.trans (Function.Embedding.subtype _)))
  · exact PMF.pure none

def allocationKernel (m : ℕ) : Kernel (Finset I) (Allocation m I) :=
  ⟨fun E ↦ (allocationPMF E m).toMeasure,measurable_of_countable _⟩
instance allocationKernel_markov (m : ℕ) : IsMarkovKernel (allocationKernel (I:=I) m) :=
  ⟨fun E ↦ by change IsProbabilityMeasure (allocationPMF E m).toMeasure; infer_instance⟩

end HardSphere.Sampling

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener CellOrbital
attribute [local instance] Classical.propDecidable
attribute [local irreducible] torusDistance

lemma endpointEligible_measurable {N K : ℕ} {L : Length} (v : Fin 3→Fin K) (s₀ : ℝ) (i : Fin N) :
    MeasurableSet {p : Configuration N L×Configuration N L | EndpointEligible v s₀ p.1 p.2 i} := by
  have h₁ : MeasurableSet {p : Configuration N L×Configuration N L | p.1 i∈centeredCell L (gridCenter L v)} :=
    (centeredCell_measurable L _).preimage ((measurable_pi_apply i).comp measurable_fst)
  have h₂ : MeasurableSet {p : Configuration N L×Configuration N L | torusDistance L (p.2 i) (gridCenter L v)≤3} :=
    measurableSet_le ((torusDistance_continuous_pair L).measurable.comp
      (f:=fun p : Configuration N L×Configuration N L ↦ (p.2 i,gridCenter L v)) (by fun_prop)) measurable_const
  have h₃ : MeasurableSet {p : Configuration N L×Configuration N L | ∀j,j≠i→
      s₀<torusDistance L (p.1 i) (p.1 j) ∧ s₀<torusDistance L (p.2 i) (p.2 j)} := by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro hj
    exact (measurableSet_lt measurable_const ((torusDistance_continuous_pair L).measurable.comp
      (f:=fun p : Configuration N L×Configuration N L ↦ (p.1 i,p.1 j)) (by fun_prop))).inter
      (measurableSet_lt measurable_const ((torusDistance_continuous_pair L).measurable.comp
      (f:=fun p : Configuration N L×Configuration N L ↦ (p.2 i,p.2 j)) (by fun_prop)))
  exact h₁.inter (h₂.inter h₃)

lemma eligible_measurable {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (v : Fin 3→Fin K) (i : Fin N) : MeasurableSet {ω | Eligible (L:=L) m r R C S s₀ u v i ω} :=
  ((endpointEligible_measurable v s₀ i).preimage
    ((continuous_eval_const 0).measurable.prodMk (continuous_eval_const 1).measurable)).inter
      (((PathCutoff.regular_measurable m r R C u S).preimage (onePathAt_continuous i).measurable).inter
        ((confined_closed (gridCenter L v)).measurableSet.preimage (onePathAt_continuous i).measurable))

def eligibleList {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (v : Fin 3→Fin K) (ω : ConfigurationPath N L) : Finset (Fin N) :=
  Finset.univ.filter (fun i ↦ Eligible m r R C S s₀ u v i ω)

lemma eligibleList_measurable {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (v : Fin 3→Fin K) : Measurable (eligibleList (N:=N) (L:=L) m r R C S s₀ u v) := by
  apply measurable_to_countable'
  intro a
  have h : eligibleList (N:=N) (L:=L) m r R C S s₀ u v ⁻¹' {a}=
      ⋂i : Fin N, {ω | (i∈a) ↔ Eligible m r R C S s₀ u v i ω} := by
    ext ω
    simp only [mem_preimage,mem_singleton_iff,mem_iInter,mem_ofPred_eq]
    constructor
    · intro h i
      rw [←h]
      simp [eligibleList]
    · intro h
      ext i
      simpa only [eligibleList,Finset.mem_filter,Finset.mem_univ,true_and] using (h i).symm
  rw [h]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i∈a
  · simpa only [hi,true_iff] using eligible_measurable (N:=N) (L:=L) m r R C S s₀ u v i
  · simpa only [hi,false_iff,←Set.compl_ofPred] using (eligible_measurable (N:=N) (L:=L) m r R C S s₀ u v i).compl

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeResidual
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators

namespace HardSphere
open Wiener

def coordinateBridge (N : ℕ) : Measure (CoordinatePaths N) := Measure.pi (fun _ ↦ bridgeLaw)
instance coordinateBridge_probability (N : ℕ) : IsProbabilityMeasure (coordinateBridge N) := by
  unfold coordinateBridge
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def gaussianCoordinates (N : ℕ) : Measure (Direction N → ℝ) := Measure.pi (fun _ ↦ gaussianReal 0 1)
instance gaussianCoordinates_probability (N : ℕ) : IsProbabilityMeasure (gaussianCoordinates N) := by
  unfold gaussianCoordinates
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_GroundBridge
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace HardSphere
open Wiener

def bridgeEndpointBase (N : ℕ) (L : Length) : Measure (BridgeEndpoints N L) :=
  (gaussianCoordinates N).prod volume

def endpointWeight {N : ℕ} {L : Length} (u : Jet N L) (t : ℝ) (e : BridgeEndpoints N L) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (t*energy u)*(‖u.1 e.2‖*‖u.1 (bridgeEnd N L t e)‖))

def endpointInteraction (N : ℕ) (L : Length) (a t : ℝ) : Set (BridgeEndpoints N L×CoordinatePaths N) :=
  endpointBridgePath N L t ⁻¹' staysAllowed N L a

def endpointWeightedBase {N : ℕ} {L : Length} (u : Jet N L) (t : ℝ) : Measure (BridgeEndpoints N L) :=
  (bridgeEndpointBase N L).withDensity (endpointWeight u t)

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeBlocks
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere
open Wiener Comparison Bridge

instance bridgeEndpointBase_finite (N : ℕ) (L : Length) : IsFiniteMeasure (bridgeEndpointBase N L) := by
  unfold bridgeEndpointBase
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance endpointWeightedBase_sfinite {N : ℕ} {L : Length} (u : Jet N L) (t : ℝ) : SFinite (endpointWeightedBase u t) := by
  unfold endpointWeightedBase bridgeEndpointBase
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PairFiber
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere
open Wiener Bridge GaussianPacking Comparison
attribute [local irreducible] torusDistance leg

def noisePairAvoid {N : ℕ} {L : Length} (a t : ℝ) (e : BridgeEndpoints N L)
    (i j : Fin N) (β γ : Bridge.Noise) : Prop :=
  ¬TrialCollision a
    (projectCurve L (leg t (labelStartLift e j) (labelEndLift t e j) γ))
    (leg t (labelStartLift e i) (labelEndLift t e i) β)

attribute [local instance] Classical.propDecidable

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_WeightedExpose
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge CellOrbital Sampling Comparison
attribute [local instance] Classical.propDecidable

def recordedList {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (v : Fin 3→Fin K)
    (p : BridgeEndpoints N L×(Fin N→Bool)) : Finset (Fin N) :=
  Finset.univ.filter (fun i ↦ gridHome hL (p.1.2 i)=v ∧ p.2 i=true)

lemma recordedList_measurable {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (v : Fin 3→Fin K) :
    Measurable (recordedList (N:=N) hL v) := by
  apply measurable_to_countable'
  intro a
  have h : recordedList (N:=N) hL v ⁻¹' {a}=
      ⋂i : Fin N,{p | (i∈a) ↔ gridHome hL (p.1.2 i)=v ∧ p.2 i=true} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_iInter,Set.mem_ofPred_eq]
    constructor
    · intro h i
      rw [←h]
      simp [recordedList]
    · intro h
      ext i
      simpa only [recordedList,Finset.mem_filter,Finset.mem_univ,true_and] using (h i).symm
  rw [h]
  apply MeasurableSet.iInter
  intro i
  have hm : MeasurableSet {p : BridgeEndpoints N L×(Fin N→Bool) |
      gridHome hL (p.1.2 i)=v ∧ p.2 i=true} :=
    (measurableSet_eq_fun ((gridHome_measurable hL).comp (by fun_prop)) measurable_const).inter
      (measurableSet_eq_fun (by fun_prop) measurable_const)
  by_cases hi : i∈a
  · simpa only [hi,true_iff] using hm
  · simpa only [hi,false_iff,←Set.compl_ofPred] using hm.compl

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GridAllocation
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison CellOrbital
attribute [local instance] Classical.propDecidable

def gridAllocationKernel {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (q : ℕ) :
    Kernel (BridgeEndpoints N L×(Fin N→Bool)) (GridAllocation N K q) :=
  finiteKernelPi (fun v : Fin 3→Fin K ↦ (allocationKernel q).comap (recordedList hL v) (recordedList_measurable hL v))

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_UnitCenter
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

def unitCenter {K : ℕ} (L : Length) (v : CubeCell K) : Torus L :=
  fun j ↦ ((pointFin ((v.1:ℝ)+1/2,(v.2.1:ℝ)+1/2,(v.2.2:ℝ)+1/2) j : ℝ) : AddCircle L.val)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_LatticeExponentialSum
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal
noncomputable section

def periodicLatticeIndex {K : ℕ} (L : Length) (x : AddCircle L.val) (v : Fin K) : ℤ :=
  (v.val:ℤ)-round (L.val⁻¹*((v.val:ℝ)+1/2-((AddCircle.equivIco L.val 0) x).val))*(K:ℤ)-
    ⌊((AddCircle.equivIco L.val 0) x).val-1/2⌋

end
end HardSphere

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FlattenLinear
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

def flattenLinear (n : ℕ) : LiftedConfiguration n→ₗ[ℝ] EuclideanConfiguration (Fin n) where
  toFun X := WithLp.toLp 2 (fun p ↦ X p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def euclideanFlatten (n : ℕ) : LiftedConfiguration n→L[ℝ] EuclideanConfiguration (Fin n) :=
  (flattenLinear n).toContinuousLinearMap

lemma realEuclidean_lift_smooth {n : ℕ} (L : Length) (f : Configuration n L→ℝ)
    (hf : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun x : EuclideanConfiguration (Fin n) ↦ f (euclideanProject L x))) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun x : LiftedConfiguration n ↦ (f (project n L x):ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hf.comp (euclideanFlatten n).contDiff)

def realEuclideanMultiplier {n : ℕ} (L : Length) (f : Configuration n L→ℝ)
    (hf : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun x : EuclideanConfiguration (Fin n) ↦ f (euclideanProject L x))) :
    SmoothMultiplier n L := SmoothMultiplier.ofSmooth (fun X ↦ (f X:ℂ)) (realEuclidean_lift_smooth L f hf)

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped Convolution NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

def mollifiedCloseRoot (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) : (ι→Torus L)→ℝ :=
  configurationMollify L φ (localCloseRoot L s v)

def mollifiedCloseCount (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) (X : ι→Torus L) : ℝ :=
  mollifiedCloseRoot L s v φ X^2

lemma mollifiedCloseRoot_smooth (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun x : EuclideanConfiguration ι ↦ mollifiedCloseRoot L s v φ (euclideanProject L x)) :=
  configurationMollify_smooth L φ _ (localCloseRoot_continuous L s v)

lemma mollifiedCloseCount_smooth (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun x : EuclideanConfiguration ι ↦ mollifiedCloseCount L s v φ (euclideanProject L x)) :=
  (mollifiedCloseRoot_smooth L s v φ).pow 2

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_MollifiedCloseCountMultiplier
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
variable {n : ℕ} [Nontrivial (Fin n)]

def mollifiedCloseCountMultiplier (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) : SmoothMultiplier n L :=
  realEuclideanMultiplier L (mollifiedCloseCount L s v φ) (mollifiedCloseCount_smooth L s v φ)

def closeHighProfile (h t : ℝ) : ℝ := 1-CellOrbital.profile h t

lemma closeHighProfile_smooth (h : ℝ) : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (closeHighProfile h) :=
  contDiff_const.sub (CellOrbital.profile_smooth h)

def mollifiedCloseCutoff (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (h : ℝ) : SmoothMultiplier n L :=
  (mollifiedCloseCountMultiplier L s v φ).realComp (closeHighProfile h) (closeHighProfile_smooth h)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_MollifiedCloseJoint
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ} [Nontrivial (Fin n)]

def mollifiedCloseJoint (L : Length) (s : ℝ)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (h : ℝ) (A : Finset (Torus L)) : SmoothMultiplier n L := by
  classical
  exact SmoothMultiplier.finsetProd A (fun v ↦ mollifiedCloseCutoff L s v φ h)

end
end HardSphere

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_UnitPairCount
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

def unitPairCount {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (X : Configuration n L) : ℝ :=
  (unitOccupation hL p v X:ℝ)*((unitOccupation hL p v X:ℝ)-1)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_WeightedUnitPairCount
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

def weightedUnitPairCount {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (X : Configuration n L) : ℝ :=
  ∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v))*unitPairCount hL (fun _ ↦ True) v X

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TorusNear
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice

def torusOffsets (R : ℕ) : Finset Vertex :=
  Fintype.piFinset fun _ : Fin 3 ↦ Finset.Icc (-(R:ℤ)) R

open MeasureTheory
variable {W V : Type*} [MeasurableSpace W] [Fintype V] [DecidableEq V]

def animalCost (G : SimpleGraph V) (B : Finset V) (w : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' m : ℕ, ∑ v : V, ∑ A∈rootedAnimals G v (m+1), if A⊆B then w (m+1) else 0

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SmoothSiteWeight
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

def smoothSiteWeight (L : Length) (A : Finset (Torus L)) (x : Torus L) : ℝ :=
  Real.exp (-smoothSpatialDistance L A x)

def smoothSiteWeightMultiplier (L : Length) (A : Finset (Torus L)) : SmoothMultiplier 1 L :=
  (spatialDistanceMultiplier L A).realComp (fun t ↦ Real.exp (-t))
    (Real.contDiff_exp.comp contDiff_id.neg)

def smoothWeightedCount {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) : ℝ :=
  ∑ i, smoothSiteWeight L A (X i)

def smoothWeightedCountMultiplier (n : ℕ) (L : Length) (A : Finset (Torus L)) : SmoothMultiplier n L :=
  SmoothMultiplier.sum (fun i : Fin n ↦ (smoothSiteWeightMultiplier L A).liftLabel n i)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ExpWeightedMultiplier
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ProbabilityTheory
open scoped ComplexConjugate
noncomputable section

def expWeightedMultiplier (n : ℕ) (L : Length) (A : Finset (Torus L)) (t : ℝ) : SmoothMultiplier n L :=
  (smoothWeightedCountMultiplier n L A).realComp (fun x ↦ Real.exp (t*x/2))
    (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).div_const 2))

end
end HardSphere

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PathPermutation
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

def permuteCoordinatePaths {n : ℕ} (σ : Equiv.Perm (Fin n))
    (w : CoordinatePaths n) : CoordinatePaths n := fun p ↦ w (σ p.1,p.2)

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_InteractingVisits
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener BathSlice _root_.OAI.HardSphere.Lattice CellOrbital

namespace ShiftVisits
open FreeVisits
attribute [local instance] Classical.propDecidable

def center {K : ℕ} (L : Length) (c : Torus L) (v : DiscreteTorus K) : Torus L := siteCenter L v+c

def singleDefect {K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (η : ℝ) (D : Set (ConfigurationPath 1 L)) (ω : ConfigurationPath 1 L) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (η*(if ω∈D then ((pathVisitedSites L (center L c) A 0 ω).card:ℝ) else 0))-1)

end ShiftVisits
end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_ShiftInteracting
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.ShiftVisits
open HardSphere.Wiener HardSphere.Lattice HardSphere.CellOrbital HardSphere.BathSlice HardSphere.FreeVisits
attribute [local irreducible] freeTrajectory
def defectiveTotalVisits {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (D : Set (ConfigurationPath 1 L)) (ω : ConfigurationPath n L) : ℕ := by
  classical
  exact ∑ i, if onePathAt i ω∈D then (pathVisitedSites L (center L c) A i ω).card else 0

end HardSphere.ShiftVisits

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.ShiftVisits
open HardSphere.Wiener HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital HardSphere.FreeVisits

def visitorCount {n K : ℕ} (L : Length) (c : Torus L) (E : Set (ConfigurationPath 1 L))
    (v : DiscreteTorus K) (ω : ConfigurationPath n L) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin n ↦ onePathAt i ω∈E ∧ pathVisitsBall L 12 (center L c v) i ω)).card

end HardSphere.ShiftVisits

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GridAlignment
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open Classical
namespace HardSphere.Groups
open CellOrbital BathSlice HardSphere.Lattice ShiftVisits

def gridCube {K : ℕ} (v : Fin 3→Fin K) : CubeCell K := (v 0,v 1,v 2)

def gridSite {K : ℕ} (v : Fin 3→Fin K) : DiscreteTorus K := fun j ↦ ((v j).val:ZMod K)

def gridShift (L : Length) : Torus L := fun _ ↦ ((-1/2:ℝ):AddCircle L.val)

end HardSphere.Groups

end
end

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open HardSphere.Lattice HardSphere.FreeVisits HardSphere.CellOrbital
attribute [local instance] Classical.propDecidable

def rangePackingBox (c : Fin 3→ℝ) : Finset Vertex :=
  Finset.Icc (fun j ↦ ⌊c j⌋-24) (fun j ↦ ⌊c j⌋+24)

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_Stationary
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HardSphere
open MeasureTheory Wiener Set Filter
open scoped ComplexConjugate ENNReal Topology BigOperators
noncomputable section
variable {N : ℕ} {L : Length}

def weightedKilledTransition (N : ℕ) (L : Length) (a t : ℝ)
    (h : ConfigurationPath N L → ℂ) (hh : MemLp h ∞ (freePathLaw N L t)) :
    ScalarL2 N L →L[ℂ] ScalarL2 N L :=
  (endpointPull N L t 0).toContinuousLinearMap.adjoint ∘L
    (L2Multiplier.clm h hh ∘L (avoidanceMultiplier N L a t ∘L
      (endpointPull N L t 1).toContinuousLinearMap))

def weightedKilledAverage (N : ℕ) (L : Length) (a t : ℝ)
    (h : ConfigurationPath N L → ℂ) (g : Configuration N L → ℂ)
    (X : Configuration N L) : ℂ :=
  ∫ w, h (freeTrajectory N L t w X)*
    killedObservable N L a g (freeTrajectory N L t w X) ∂coordinateWiener N

lemma weightedKilledAverage_measurable (N : ℕ) (L : Length) (a t : ℝ)
    {h : ConfigurationPath N L → ℂ} (hh : Measurable h)
    {g : Configuration N L → ℂ} (hg : Measurable g) :
    Measurable (weightedKilledAverage N L a t h g) := by
  exact (((hh.mul (killedObservable_measurable N L a hg)).comp
    (freeTrajectory_continuous N L t).measurable).stronglyMeasurable.integral_prod_left').measurable

lemma weightedKilledAverage_bound (N : ℕ) (L : Length) (a t : ℝ)
    {h : ConfigurationPath N L → ℂ} {B : ℝ} (hB : 0≤B) (hhB : ∀ ω, ‖h ω‖≤B)
    {g : Configuration N L → ℂ} {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C)
    (X : Configuration N L) : ‖weightedKilledAverage N L a t h g X‖≤B*C := by
  have hb (w : CoordinatePaths N) : ‖h (freeTrajectory N L t w X)*
      killedObservable N L a g (freeTrajectory N L t w X)‖≤B*C := by
    rw [norm_mul]
    exact mul_le_mul (hhB _) (killedObservable_bound N L a hC hgC _) (norm_nonneg _) hB
  simpa only [weightedKilledAverage,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
    norm_integral_le_of_norm_le_const (μ := coordinateWiener N) (Eventually.of_forall hb)

lemma weightedKilledAverage_memLp (N : ℕ) (L : Length) (a t : ℝ)
    {h : ConfigurationPath N L → ℂ} (hh : Measurable h)
    {B : ℝ} (hB : 0≤B) (hhB : ∀ ω, ‖h ω‖≤B)
    {g : Configuration N L → ℂ} (hg : Measurable g)
    {C : ℝ} (hC : 0≤C) (hgC : ∀ X, ‖g X‖≤C) :
    MemLp (weightedKilledAverage N L a t h g) 2 (volume : Measure (Configuration N L)) :=
  MemLp.of_bound (weightedKilledAverage_measurable N L a t hh hg).aestronglyMeasurable (B*C)
    (Eventually.of_forall (weightedKilledAverage_bound N L a t hB hhB hC hgC))

end

end HardSphere

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SiteGroups
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Sampling
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

def siteAllocationKernel (total : ℕ) :
    Kernel (V→Finset I) (V→Allocation total I) :=
  ⟨fun E ↦ Measure.pi (fun v ↦ (allocationPMF (E v) total).toMeasure),measurable_of_countable _⟩

instance siteAllocationKernel_markov (total : ℕ) :
    IsMarkovKernel (siteAllocationKernel (V:=V) (I:=I) total) :=
  ⟨fun _ ↦ by change IsProbabilityMeasure (Measure.pi _); infer_instance⟩

end HardSphere.Sampling

namespace HardSphere.Groups
open Sampling Wiener PathCutoff

def physicalAllocationKernel {N K : ℕ} {L : Length} (m total : ℕ)
    (r R C S s₀ : ℝ) (u : Time) :
    Kernel (ConfigurationPath N L) ((Fin 3→Fin K)→Allocation total (Fin N)) :=
  (siteAllocationKernel total).comap
    (fun ω v ↦ eligibleList m r R C S s₀ u v ω)
    (Measurable.of_eval (fun v ↦ eligibleList_measurable m r R C S s₀ u v))

instance physicalAllocationKernel_markov {N K : ℕ} {L : Length} (m total : ℕ)
    (r R C S s₀ : ℝ) (u : Time) :
    IsMarkovKernel (physicalAllocationKernel (N:=N) (K:=K) (L:=L) m total r R C S s₀ u) := by
  unfold physicalAllocationKernel
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalDatum
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def physicalDatum {N K M G : ℕ} {L : Length} (g : Fin G)
    (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (z : ConfigurationPath N L × GridAllocation N K (G*M)) : PhysicalDatum N K M G L :=
  (z.1 0,z.1 1,(fun i ↦ decide (∃v : Fin 3 → Fin K,
    Eligible m r R C S s₀ u v i z.1)),z.2,
    fun i ↦ if i∈groupUnion g z.2 then 0 else onePathAt i z.1)

def physicalDatumLaw {N K M G : ℕ} {L : Length} (g : Fin G)
    (ψ : Jet N L) (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    Measure (PhysicalDatum N K M G L) :=
  ((groundPathLaw N L r T ψ).compProd
    (physicalAllocationKernel (K:=K) m (G*M) r R C S s₀ u)).map
      (physicalDatum g m r R C S s₀ u)

attribute [local irreducible] TrialCollision

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_CoarsePhysical
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def physicalBranchDatum {N K M G : ℕ} {L : Length} (g : Fin G)
    (b : Fin N→Bool) (a : GridAllocation N K (G*M)) (T : ℝ)
    (w : BridgeEndpoints N L × ({i // i∉groupUnion g a}→Bridge.Noise)) :
    PhysicalDatum N K M G L :=
  (w.1.2,bridgeEnd N L T w.1,b,a,fun i ↦ if hi : i∈groupUnion g a then 0 else
    frozenPaths T w.1 (fun j ↦ j∈groupUnion g a) w.2 ⟨i,hi⟩)

end HardSphere.Groups

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def projectGroup {I : Type*} {L : Length} (f : I→C(Time,Point)) :
    I→ ConfigurationPath 1 L := fun i ↦ projectCurve L (f i)

def selectedPhysicalPath {N : ℕ} {L : Length} (T : ℝ) (p : Fin N→Prop)
    (v : (BridgeEndpoints N L × ({i // ¬p i}→Bridge.Noise)) × ({i // p i}→Bridge.Noise)) :
    {i // p i}→ ConfigurationPath 1 L :=
  fun i ↦ onePathAt i (labelBridgePath N L T (blockGlue p v))

def datumPhysicalReference {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S t : ℝ) (u : Time) :
    Kernel (PhysicalDatum N K M G L) ({i // i∈groupUnion g a}→ ConfigurationPath 1 L) :=
  (datumGroupReference hL g a m r R C S t u).map projectGroup
instance datumPhysicalReference_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S t : ℝ) (u : Time) :
    IsFiniteKernel (datumPhysicalReference hL g a m r R C S t u) := by
  unfold datumPhysicalReference
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalVertex
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

instance vertexPair_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i i' : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) :
    IsFiniteKernel (vertexPair (M:=M) hL g m t r R C S u i i' v w j) := by
  unfold vertexPair exposedPeriodPair exposedPairedTrialKernel parameterPairedKernel
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_AddedSites
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace HardSphere.Lattice

def addedSites {K : ℕ} (H : Finset (DiscreteTorus K)) : Finset (DiscreteTorus K) :=
  H.biUnion fun c ↦ ((torusOffsets 1).erase 0).image (fun d ↦ c+torusProjection K d)

end HardSphere.Lattice

open scoped BigOperators Classical

open scoped BigOperators Classical

namespace HardSphere.Lattice

def torusContact {K : ℕ} (R : ℕ) (H Γ : Finset (DiscreteTorus K)) : Prop :=
  ∃ c∈H, ∃ z∈Γ, torusNear K R c z

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalRouteGeometry
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice

def siteIndexEquiv {K : ℕ} [NeZero K] : DiscreteTorus K ≃ (Fin 3→Fin K) :=
  ⟨siteIndex,indexSite,indexSite_siteIndex,siteIndex_indexSite⟩

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalEndpoint
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

instance endpointPair_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) :
    IsFiniteKernel (endpointPair (M:=M) hL g m t r R C S u i v w j) := by
  unfold endpointPair
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalRouteFactors
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

instance physicalRouteFactor_finite {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (labels : Fin (n+1)↪Fin N) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (k : Fin (n+2)) :
    IsFiniteKernel (physicalRouteFactor (M:=M) hL g m t r R C S u labels v steps k) := by
  unfold physicalRouteFactor
  split_ifs <;> infer_instance

def routeFirstReference {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (labels : Fin (n+1)↪Fin N) (v : Fin (n+2)→(Fin 3→Fin K))
    (k : Fin (n+2)) (d : PhysicalDatum N K M G L) : Measure C(Time,Point) :=
  if hk : k.val<n+1 then datumIndividualReference hL g m r R C S t u (labels ⟨k.val,hk⟩) d
  else cellPathReference (v k)

def routeSecondReference {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (labels : Fin (n+1)↪Fin N) (v : Fin (n+2)→(Fin 3→Fin K))
    (k : Fin (n+2)) (d : PhysicalDatum N K M G L) : Measure C(Time,Point) :=
  if h0 : k.val=0 then cellPathReference (v k)
  else datumIndividualReference hL g m r R C S t u (labels ⟨k.val-1,by omega⟩) d

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PhysicalRoute
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*}

def physicalSlotReference {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) :
    Option J→Kernel (PhysicalDatum N K M G L) C(Time,Point)
  | none => Kernel.const _ (cellPathReference v)
  | some i => datumIndividualReference hL g m r R C S t u (particle i)

instance physicalSlotReference_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (i : Option J) :
    IsFiniteKernel (physicalSlotReference (M:=M) hL g m t r R C S u particle v i) := by
  cases i <;> dsimp only [physicalSlotReference] <;> infer_instance

instance physicalSelectedFactor_finite {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (i : routeSlots labels) :
    IsFiniteKernel (physicalSelectedFactor (M:=M) hL g m t r R C S u particle labels v steps i) :=
  physicalRouteFactor_finite ..

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalPrimary
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalSlotMutual {L : Length} (r : ℝ) : Set (Option J→C(Time,Point)) :=
  (fun x ↦ fun i ↦ x (some i)) ⁻¹' physicalMutual (L:=L) r

def physicalPrimaryReference {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) :
    Kernel (PhysicalDatum N K M G L) (Option J→C(Time,Point)) :=
  fiberNormalize (finiteKernelPi (physicalSlotReference hL g m t r R C S u particle v))
    (Prod.snd ⁻¹' physicalSlotMutual (L:=L) r)

instance physicalPrimaryReference_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) :
    IsFiniteKernel (physicalPrimaryReference (M:=M) hL g m t r R C S u particle v) := by
  unfold physicalPrimaryReference; infer_instance

def physicalSharedRoute {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) :
    Kernel (PhysicalDatum N K M G L)
      ((Option J→C(Time,Point))×(routeSlots labels→C(Time,Point)×C(Time,Point))) :=
  ambientSharedKernel (routeSlots labels) (routePermutation labels) (routePermutation_fixed labels)
    (physicalPrimaryReference hL g m t r R C S u particle (v (Fin.last (n+1))))
    (physicalSelectedFactor hL g m t r R C S u particle labels v steps)
    (Prod.snd ⁻¹' physicalSlotMutual (L:=L) r)

instance physicalSharedRoute_finite {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) :
    IsFiniteKernel (physicalSharedRoute (M:=M) hL g m t r R C S u particle labels v steps) := by
  unfold physicalSharedRoute; infer_instance

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalLifted
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

instance physicalSelectedOn_finite {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L) (i : routeSlots labels) :
    IsFiniteMeasure (physicalSelectedOn hL g m t r R C S u particle labels v steps d i) := by
  unfold physicalSelectedOn supportedPair
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def physicalOnPrimary {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :=
  conditionedMeasure (Measure.pi (physicalSlotOn hL g m t r R C S u particle v d))
    (retainedEvent (physicalOnChecks hL g m r R C S u particle d) Finset.univ)

instance physicalOnPrimary_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :
    IsFiniteMeasure (physicalOnPrimary hL g m t r R C S u particle v d) := by
  unfold physicalOnPrimary; infer_instance

def physicalSharedOn {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L) :=
  ambientSharedKernel (routeSlots labels) (routePermutation labels) (routePermutation_fixed labels)
    (Kernel.const Unit (physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d))
    (fun i ↦ Kernel.const Unit (physicalSelectedOn hL g m t r R C S u particle labels v steps d i))
    (Prod.snd ⁻¹' retainedEvent (physicalOnChecks hL g m r R C S u particle d) Finset.univ) ()

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalPairedRoute
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalPairedRoute {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) :
    Kernel (PhysicalDatum N K M G L) ((Option J→C(Time,Point))×(Option J→C(Time,Point))) :=
  (physicalSharedRoute hL g m t r R C S u particle labels v steps).map
    (fun z ↦ (ambientFirst (routeSlots labels) (routePermutation labels) z,
      ambientSecond (routeSlots labels) (routePermutation labels) (routePermutation_fixed labels) z))

instance physicalPairedRoute_finite {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) : IsFiniteKernel (physicalPairedRoute (M:=M) hL g m t r R C S u particle labels v steps) := by
  unfold physicalPairedRoute; infer_instance

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PhaseMeasure
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

def localLiftBox {N : ℕ} (L : Length) (c : LiftedConfiguration N) : Set (LiftedConfiguration N) :=
  Set.univ.pi (fun i ↦ Set.univ.pi (fun j ↦ Icc (c i j-L.val/2) (c i j+L.val/2)))

def flattenEquiv (N : ℕ) : LiftedConfiguration N ≃L[ℝ] (Direction N → ℝ) :=
  (LinearEquiv.curry ℝ ℝ (Fin N) (Fin 3)).symm.toContinuousLinearEquiv

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhaseBridge
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

def liftedBridgePath {N : ℕ} (t : ℝ) (X Y : LiftedConfiguration N) (β : CoordinatePaths N) :
    C(Time,LiftedConfiguration N) :=
  ⟨fun s i j ↦ (1-(s:ℝ))*X i j+(s:ℝ)*Y i j+Real.sqrt (2*t)*β (i,j) s,by fun_prop⟩

def projectedBridgePath {N : ℕ} (L : Length) (t : ℝ) (X Y : LiftedConfiguration N) (β : CoordinatePaths N) :
    ConfigurationPath N L :=
  ⟨fun s ↦ project N L (liftedBridgePath t X Y β s),(continuous_project N L).comp (liftedBridgePath t X Y β).continuous⟩

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_TorusLocalBridge
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

def localLiftChart {N : ℕ} (L : Length) (c : LiftedConfiguration N) : Set (LiftedConfiguration N) :=
  univ.pi (fun i ↦ univ.pi (fun j ↦ Ioc (c i j-L.val/2) (c i j-L.val/2+L.val)))

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_Phase
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate

namespace HardSphere

def groundPhaseRepresentative {N : ℕ} {L : Length} (u : Jet N L) : Configuration N L → ℂ :=
  LocalAE.representative volume (fun y ↦ complexPhase (u.1 y))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_PhysicalCollision
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

def datumCollisionBound (t r h R C : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (9/10:ℝ)*(ENNReal.ofReal (99/100:ℝ)*midpointLower t 13))⁻¹ *
    (2*ENNReal.ofReal (hitConstant*(4*C*(2*t)*r+8*r*(1+R)^3/Real.sqrt (h/2))))

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalAmbientRN
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

instance physicalSharedOn_finite {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→Fin 3→Fin K)
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L) :
    IsFiniteMeasure (physicalSharedOn hL g m t r R C S u particle labels v steps d) := by
  unfold physicalSharedOn
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalBranchLaw
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

attribute [local irreducible] datumGroupReference datumIndividualReference

def physicalBranchLaw {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) : Measure (PhysicalDatum N K M G L) :=
  (exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
    (fun _ : Fin N ↦ Bridge.law) (fun i ↦ i∈groupUnion g a)
    (labelInteraction N L r T∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ T u) b)).map
      (physicalBranchDatum g b a T)
instance physicalBranchLaw_sfinite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    SFinite (physicalBranchLaw hL μ g b a m r R C S s₀ T u) := by
  unfold physicalBranchLaw exposedLaw; infer_instance

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalSupply
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def fullFailure {N K : ℕ} {L : Length} (n : ℕ) (t r R C S : ℝ) (w : Time)
    (v : Fin 3 → Fin K) (ω : ConfigurationPath N L) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ ¬StrongExcept n t r R C S w
    (nearestLift L (anchorPoint v) (ω 0 i)) (nearestLift L (anchorPoint v) (ω 1 i))
    (anchorPoint v) (fun j ↦ onePathAt j ω) i (fun j ↦ unitTarget (anchorPoint v+targetStep j))

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalLabelLaw
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
instance labelOptionSingletons (J : Type*) : MeasurableSingletonClass (Option J) := ⟨fun _ ↦ trivial⟩

variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma paddedLabels_nonempty (s : Finset J) : (paddedLabels s).Nonempty := by
  by_cases h : s.Nonempty
  · simpa only [paddedLabels,ite_eq_left h] using h.image some
  · simp [paddedLabels,h]

def uniformLabels (s : Finset J) : Measure (Option J) :=
  (PMF.uniformOfFinset (paddedLabels s) (paddedLabels_nonempty s)).toMeasure
instance uniformLabels_probability (s : Finset J) : IsProbabilityMeasure (uniformLabels s) := by
  unfold uniformLabels; infer_instance

def physicalLabelAt {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (v : DiscreteTorus K) : Kernel (PhysicalDatum N K M G L) (Option J) where
  toFun d := uniformLabels (branchAccessible hL g m t r R C S u particle v d)
  measurable' := (measurable_of_countable (f:=uniformLabels (J:=J))).comp
    (branchAccessible_measurable hL g m t r R C S u particle v)

instance physicalLabelAt_markov {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (v : DiscreteTorus K) : IsMarkovKernel (physicalLabelAt (M:=M) hL g m t r R C S u particle v) :=
  ⟨fun _ ↦ inferInstanceAs (IsProbabilityMeasure (uniformLabels _))⟩

def physicalLabels {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N) :
    Kernel (PhysicalDatum N K M G L) (DiscreteTorus K→Option J) :=
  finiteKernelPi (physicalLabelAt hL g m t r R C S u particle)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TorusBall
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice

def torusBall {K : ℕ} [NeZero K] (R : ℕ) (x : DiscreteTorus K) : Finset (DiscreteTorus K) :=
  Finset.univ.filter (torusNear K R x)

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EndpointDanger
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
open scoped ENNReal
namespace HardSphere.Lattice

def endpointDanger {K : ℕ} [NeZero K] (B : Finset (DiscreteTorus K)) (x : DiscreteTorus K) : Prop :=
  ∃ F∈candidateSets (torusRangeGraph K 1), F⊆B ∧ ∃ c∈F, torusNear K F.card x c

def endpointAnimals {K : ℕ} [NeZero K] (x : DiscreteTorus K) (m : ℕ) : Finset (Finset (DiscreteTorus K)) :=
  (torusBall m x).biUnion (fun c ↦ rootedAnimals (torusRangeGraph K 1) c m)

open scoped NNReal

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SimplePath
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalLabelAt_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
open scoped ENNReal
namespace HardSphere.Lattice
open MeasureTheory ProbabilityTheory

instance simplePathCountable {K : ℕ} [NeZero K] (x y : DiscreteTorus K) :
    Countable (SimplePath x y) := by
  let : Countable ((torusNearestGraph K).Walk x y) := SimpleGraph.Walk.support_injective.countable
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance environmentMeasurableSpace (K : ℕ) : MeasurableSpace (Finset (DiscreteTorus K)) := ⊤

def simplePathGood {K : ℕ} (B : Finset (DiscreteTorus K)) {x y : DiscreteTorus K}
    (p : SimplePath x y) : Prop := ∀ z∈p.val.support, z∉B

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_SimpleRouteGeometry
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K} {J : Type*}

def simpleRouteVertices (p : SimplePath x y) (n : ℕ) : Fin (n+2)→Fin 3→Fin K :=
  fun i ↦ siteIndex (p.val.getVert i.val)

omit [NeZero K] in
lemma simpleRouteVertices_adjacent (p : SimplePath x y) (n : ℕ) (hn : n+1=p.val.length)
    (i : Fin (n+1)) :
    (torusNearestGraph K).Adj (p.val.getVert i.castSucc.val) (p.val.getVert i.succ.val) :=
  p.val.adj_getVert_succ (by simpa only [Fin.val_castSucc, ←hn] using i.isLt)

def simpleRouteSteps {L : Length} (hL : L.val=(K:ℝ))
    (p : SimplePath x y) (n : ℕ) (hn : n+1=p.val.length) : Fin (n+1)→Fin 7 :=
  fun i ↦ (adjacent_routeCellPeriod hL (simpleRouteVertices_adjacent p n hn i)).choose

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_RouteFields
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalSharedOn_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

def fieldLabels (p : SimplePath x y) (z : DiscreteTorus K→Option J) (h : RouteFieldValid p z) : Fin p.val.length↪J := h.choose

omit [NeZero K] in
lemma simpleRouteLength_eq (hxy : x≠y) (p : SimplePath x y) : p.val.length-1+1=p.val.length := by
  have hp : p.val.length≠0 := fun h ↦ hxy (SimpleGraph.Walk.eq_of_length_eq_zero h)
  omega

def fieldRouteLabels (hxy : x≠y) (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (h : RouteFieldValid p z) : Fin (p.val.length-1+1)↪J :=
  (finCongr (simpleRouteLength_eq hxy p)).toEmbedding.trans (fieldLabels p z h)

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalCodedRoute {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (c : PhysicalRouteCode x y J) :
    Kernel (PhysicalDatum N K M G L) ((Option J→C(Time,Point))×(Option J→C(Time,Point))) :=
  if h : RouteFieldValid c.1 c.2 then
    physicalPairedRoute hL g m t r R C S u particle (fieldRouteLabels hxy c.1 c.2 h)
      (simpleRouteVertices c.1 (c.1.val.length-1))
      (simpleRouteSteps hL c.1 (c.1.val.length-1) (simpleRouteLength_eq hxy c.1))
  else 0

def physicalRouteFamily {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) :
    Kernel (PhysicalDatum N K M G L × PhysicalRouteCode x y J)
      ((Option J→C(Time,Point))×(Option J→C(Time,Point))) where
  toFun z := physicalCodedRoute hL g m t r R C S u particle hxy z.2 z.1
  measurable' := measurable_from_prod_countable_left fun c ↦
    (physicalCodedRoute hL g m t r R C S u particle hxy c).measurable

def physicalMixedRoutes {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsMarkovKernel ν] :
    Kernel (PhysicalDatum N K M G L)
      (PhysicalRouteCode x y J × ((Option J→C(Time,Point))×(Option J→C(Time,Point)))) :=
  (ν.prod (physicalLabels hL g m t r R C S u particle)) ⊗ₖ
    physicalRouteFamily hL g m t r R C S u particle hxy

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalFamilyLikelihood
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalSharedOn_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalRouteView {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) :=
  (physicalRouteFamily (M:=M) hL g m t r R C S u particle hxy).map
    (if b then Prod.fst else Prod.snd)

def physicalFamilyReference {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N) (b : Bool) :
    Kernel (PhysicalDatum N K M G L×PhysicalRouteCode x y J) (Option J→C(Time,Point)) :=
  (physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x))).comap
    Prod.fst measurable_fst
instance physicalFamilyReference_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N) (b : Bool) :
    IsFiniteKernel (physicalFamilyReference (M:=M) (x:=x) (y:=y) hL g m t r R C S u particle b) := by
  unfold physicalFamilyReference; infer_instance

def physicalRouteLikelihood {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) :=
  Kernel.rnDeriv (physicalRouteView (M:=M) hL g m t r R C S u particle hxy b)
    (physicalFamilyReference hL g m t r R C S u particle b)

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Comparison HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def fieldLabelImage (p : SimplePath x y) (z : DiscreteTorus K→Option J) : Finset (Option J) :=
  Finset.univ.image (fun i : Fin p.val.length ↦ z (pathVertexEmbedding p i.castSucc))

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PhysicalObservation
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalSharedOn_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalFullMidpoint {N K M G : ℕ} {L : Length} (particle : J↪Fin N)
    (z : PhysicalDatum N K M G L×(Option J→C(Time,Point))) : Option (Fin N)→Torus L :=
  fillGroup particle (fun i ↦ i.elim 0 (fun j ↦ z.1.2.2.2.2 j midpointTime 0))
    (fun i ↦ projectPoint L (z.2 i midpointTime))

omit [Fintype J] [DecidableEq J] in
lemma physicalFullMidpoint_measurable {N K M G : ℕ} {L : Length} (particle : J↪Fin N) :
    Measurable (physicalFullMidpoint (K:=K) (M:=M) (G:=G) (L:=L) particle) := by
  unfold physicalFullMidpoint
  refine (fillGroup_measurable (E:=Torus L) particle).comp (f:=fun z : PhysicalDatum N K M G L×(Option J→C(Time,Point)) ↦
    ((fun i : Option (Fin N) ↦ i.elim 0 (fun j ↦ z.1.2.2.2.2 j midpointTime 0)),
     (fun i : Option J ↦ projectPoint L (z.2 i midpointTime)))) ?_
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro i
    cases i with
    | none => exact measurable_const
    | some i =>
      exact (measurable_pi_apply 0).comp ((continuous_eval_const midpointTime).measurable.comp
        ((datumFrozen_measurable i).comp measurable_fst))
  · apply Measurable.of_eval
    intro i
    exact (projectPoint_continuous L).measurable.comp ((continuous_eval_const midpointTime).measurable.comp
      ((measurable_pi_apply i).comp measurable_snd))

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_PhysicalObservedLaw
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalSharedOn_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalBathKernel {N K M G : ℕ} {L : Length} (particle : J↪Fin (N+1))
    (b : Bool) (i : J) :
    Kernel (PhysicalDatum (N+1) K M G L×(Option J→C(Time,Point)))
      (Torus L×Torus L×(Fin N→Torus L)) :=
  (primaryBathKernel b (particle i)).comap (physicalFullMidpoint particle)
    (physicalFullMidpoint_measurable particle)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalMixedObservation
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalCodeTag {N : ℕ} (particle : J↪Fin (N+1)) (hxy : x≠y)
    (b : Bool) (c : PhysicalRouteCode x y J) : Fin (N+1) :=
  if h : RouteFieldValid c.1 c.2 then
    particle (fieldRouteLabels hxy c.1 c.2 h (if b then 0 else Fin.last (c.1.val.length-1)))
  else 0

def taggedPhysicalBathKernel {N M G : ℕ} {L : Length} (particle : J↪Fin (N+1)) (b : Bool) :
    Kernel (Fin (N+1)×(PhysicalDatum (N+1) K M G L×(Option J→C(Time,Point))))
      (Torus L×Torus L×(Fin N→Torus L)) where
  toFun z := primaryBathKernel b z.1 (physicalFullMidpoint particle z.2)
  measurable' := measurable_from_prod_countable_right fun i ↦
    (primaryBathKernel b i).measurable.comp (physicalFullMidpoint_measurable particle)

def physicalCodeObserver {N M G : ℕ} {L : Length} (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool) :
    Kernel (PhysicalDatum (N+1) K M G L×(PhysicalRouteCode x y J×((Option J→C(Time,Point))×(Option J→C(Time,Point)))))
      (Torus L×Torus L×(Fin N→Torus L)) :=
  (taggedPhysicalBathKernel particle b).comap
    (fun z ↦ (physicalCodeTag particle hxy b z.2.1,(z.1,if b then z.2.2.1 else z.2.2.2)))
    (by
      apply Measurable.prodMk
      · exact (measurable_of_countable (physicalCodeTag particle hxy b)).comp measurable_snd.fst
      · cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> exact measurable_fst.prodMk (by fun_prop))

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalTagEvent {N M G : ℕ} {L : Length} (particle : J↪Fin N)
    (v : Fin 3→Fin K) (i : Fin N) : Set (PhysicalDatum N K M G L×(Option J→C(Time,Point))) :=
  {z | i∈Set.range particle ∧ physicalFullMidpoint particle z (some i)∈centeredCell L (gridCenter L v)}

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalMidpointReference
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def rawPhysicalBranch {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (_group : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :=
  ((allocationBase μ (gridAllocationKernel hL (G*M)) b a).prod
    (Measure.pi fun _ : Fin N ↦ Bridge.law)).restrict
      (labelInteraction N L r T∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ T u) b)
instance rawPhysicalBranch_sfinite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    SFinite (rawPhysicalBranch hL μ g b a m r R C S s₀ T u) := by
  unfold rawPhysicalBranch; infer_instance

def physicalRecoveredPath {N K M G : ℕ} {L : Length} (g : Fin G)
    (a : GridAllocation N K (G*M))
    (z : PhysicalDatum N K M G L×({i // i∈groupUnion g a}→ ConfigurationPath 1 L)) :
    Fin N→ ConfigurationPath 1 L :=
  fun i ↦ if hi : i∈groupUnion g a then z.2 ⟨i,hi⟩ else z.1.2.2.2.2 i

def physicalRecoveredMidpoint {N K M G : ℕ} {L : Length} (g : Fin G)
    (a : GridAllocation N K (G*M))
    (z : PhysicalDatum N K M G L×({i // i∈groupUnion g a}→ ConfigurationPath 1 L)) : Configuration N L :=
  fun i ↦ physicalRecoveredPath g a z i midpointTime 0

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalReferenceRaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
attribute [local instance] Comparison.permBathSpace Comparison.permBathSingleton

def physicalCellPost {N K : ℕ} (L : Length) (extra tag : Fin 3→Fin K) (b : Bool) :
    Kernel (Torus L×Configuration N L) (Torus L×Torus L×Configuration N L) :=
  (cellExtraKernel (cellPointReference L extra) (centeredCell L (gridCenter L tag)) univ
    (centeredCell_measurable L _)).map (cellObservation b)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_AllocatedLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
attribute [local instance] Comparison.permBathSpace Comparison.permBathSingleton

def physicalRead {N K M G : ℕ} (L : Length) (extra tag : Fin 3→Fin K) (b : Bool)
    (i : Fin (N+1)) : Kernel (ConfigurationPath (N+1) L×GridAllocation (N+1) K (G*M))
      (Torus L×Torus L×Configuration N L) :=
  ((physicalCellPost L extra tag b) ∘ₖ orderedKernel (uniformBathOrder N) i).comap
    (fun p ↦ p.1 midpointTime) ((continuous_eval_const midpointTime).measurable.comp measurable_fst)

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

def physicalCellVolumePost {N K : ℕ} (L : Length) (extra tag : Fin 3→Fin K) (b : Bool) :
    Kernel (Torus L×Configuration N L) (Torus L×Torus L×Configuration N L) :=
  (cellExtraKernel volume (centeredCell L (gridCenter L tag))
    (centeredCell L (gridCenter L extra)) (centeredCell_measurable L _)).map (cellObservation b)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_CertificateSix
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open PathCutoff FreeVisits CellOrbital BathSlice Wiener HardSphere.Lattice

def certificateBad {N K : ℕ} [Nontrivial (Fin N)] {L : Length}
    (m : ℕ) (r R C S s₀ ell θ H D : ℝ) (u : Time) (i : Fin 6)
    (v : Fin 3→Fin K) (ω : ConfigurationPath N L) : Prop :=
  ![(centeredCount L (gridCenter L v) (ω 0):ℝ)<ell*D,
    θ*D≤((localCloseLabels L s₀ (gridCenter L v) (ω 0)).card:ℝ),
    θ*D≤((localCloseLabels L s₀ (gridCenter L v) (ω 1)).card:ℝ),
    H*D<((visitors (gridCenter L v) ω).card:ℝ),
    ¬(∀i,pathVisitsBall L 12 (gridCenter L v) i ω→Regular m r R C u S (onePathAt i ω)),
    θ*D≤((longVisitors (gridCenter L v) ω).card:ℝ)] i

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalAverageMoment
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def physicalAverageLikelihood {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y))
    (d : PhysicalDatum N K M G L) (w : Option J→C(Time,Point)) : ℝ≥0∞ :=
  ∫⁻c,physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,c) w
    ∂(ν.prod (physicalLabels hL g m t r R C S u particle)) d

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def physicalGoodLikelihood {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y))
    (E : Set (PhysicalDatum N K M G L)) (z : PhysicalDatum N K M G L×(Option J→C(Time,Point))) : ℝ≥0∞ :=
  if z.1∈E then physicalAverageLikelihood hL g m t r R C S u particle hxy b ν z.1 z.2 else 0

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalBranchEstimates
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
attribute [local irreducible] datumHome datumSelected groupUnion datumStart datumEnd anchorPoint

def latticeDatumBad {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (d : PhysicalDatum N K M G L) :
    Finset (DiscreteTorus K) := (datumBad hL g m t r R C S u d).image indexSite

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalObservedMixture
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalObservedMixture {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (b : Bool) : Kernel (PhysicalDatum (N+1) K M G L) (Torus L×Torus L×(Fin N→Torus L)) :=
  ((physicalMixedRoutes hL g m t r R C S u particle hxy ν) ⊗ₖ
    physicalCodeObserver particle hxy b).snd

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalTaggedDensity
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def physicalTaggedMixture {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) (E : Set (PhysicalDatum (N+1) K M G L)) :=
  (((μ.restrict E).compProd ((ν.prod (physicalLabels hL g m t r R C S u particle))⊗ₖ
    physicalRouteView hL g m t r R C S u particle hxy b)).map
      (fun z ↦ (physicalCodeTag particle hxy b z.2.1,(z.1,z.2.2))))

def physicalTagLikelihood {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y))
    (E : Set (PhysicalDatum (N+1) K M G L)) :=
  conditionalTagLikelihood (ν.prod (physicalLabels hL g m t r R C S u particle))
    (physicalCodeTag particle hxy b)
    (fun z ↦ physicalRouteLikelihood hL g m t r R C S u particle hxy b z.1 z.2) E

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def physicalTaggedReference {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (b : Bool) (μ : Measure (PhysicalDatum (N+1) K M G L)) :=
  taggedReference (μ.compProd (physicalPrimaryReference hL g m t r R C S u particle
    (siteIndex (if b then y else x)))) (physicalTagEvent particle (siteIndex (if b then x else y)))

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalTaggedObservation
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def retainedTaggedPhysicalBath {N M G : ℕ} {L : Length} (particle : J↪Fin (N+1)) (b : Bool) :=
  (Kernel.deterministic (fun z : Fin (N+1)×(PhysicalDatum (N+1) K M G L×(Option J→C(Time,Point))) ↦ z.2.1)
    measurable_snd.fst) ×ₖ taggedPhysicalBathKernel particle b

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalObservedMass
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

instance physicalTaggedReference_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (b : Bool) (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ) := by
  unfold physicalTaggedReference taggedReference
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def physicalCommonObserved {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) (E : Set (PhysicalDatum (N+1) K M G L)) :=
  taggedPhysicalBathKernel particle false ∘ₘ physicalTaggedMixture hL g m t r R C S u particle hxy false ν μ E

def physicalObservedReference {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (b : Bool) (μ : Measure (PhysicalDatum (N+1) K M G L)) :=
  taggedPhysicalBathKernel particle b ∘ₘ physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalGroupComparison
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}

def physicalGroupReference {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (ψ : Jet (N+1) L) (g : Fin G) (m : ℕ) (t r R C S s₀ : ℝ) (u : Time) (b : Bool) :=
  ∑flags,∑a : GridAllocation (N+1) K (G*M),
    physicalObservedReference (x:=x) (y:=y) hL g m t r R C S u (branchParticles g a) b
      (physicalBranchLaw hL (endpointWeightedBase ψ (2*t)) g flags a m r R C S s₀ (2*t) u)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ScalarNormSqIntegral
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace HardSphere

lemma scalar_norm_sq_integral {N : ℕ} {L : Length} (u : ScalarL2 N L) :
    ‖u‖^2 = ∫ X, ‖u X‖^2 := by
  rw [← real_inner_self_eq_norm_sq (F := ScalarL2 N L), L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

end HardSphere

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Rescaling_PhysicalRescaling
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere
namespace Rescaling
attribute [local instance] Classical.propDecidable

def circle (L J : Length) : AddCircle L.val ≃+ AddCircle J.val :=
  AddCircle.equivAddCircle L.val J.val L.property.ne' J.property.ne'
def torus (L J : Length) : Torus L ≃+ Torus J := AddEquiv.piCongrRight fun _ ↦ circle L J
def config (N : ℕ) (L J : Length) : Configuration N L ≃+ Configuration N J :=
  AddEquiv.piCongrRight fun _ ↦ torus L J
def configHomeo (N : ℕ) (L J : Length) : Configuration N L ≃ₜ Configuration N J :=
  Homeomorph.piCongrRight fun _ ↦ Homeomorph.piCongrRight fun _ ↦
    AddCircle.homeomorphAddCircle L.val J.val L.property.ne' J.property.ne'

lemma config_continuous (N : ℕ) (L J : Length) : Continuous (config N L J) := (configHomeo N L J).continuous

lemma circle_project (L J : Length) (x : ℝ) : circle L J (x : AddCircle L.val)=((J.val/L.val*x : ℝ) : AddCircle J.val) := by
  simp only [circle,AddCircle.equivAddCircle_apply_mk]
  congr 1
  ring
lemma config_project (N : ℕ) (L J : Length) (X : LiftedConfiguration N) :
    config N L J (project N L X)=project N J ((J.val/L.val) • X) := by
  ext i j
  exact circle_project L J _

lemma circle_representative (L J : Length) (x : AddCircle L.val) :
    (AddCircle.equivIco J.val 0 (circle L J x)).val=
      J.val/L.val*(AddCircle.equivIco L.val 0 x).val := by
  have hLp := L.property
  have hJp := J.property
  let y := (AddCircle.equivIco L.val 0 x).val
  have hy : y∈Ico 0 L.val := by simpa only [zero_add] using (AddCircle.equivIco L.val 0 x).property
  have he : x=(y : AddCircle L.val) := AddCircle.coe_equivIco.symm
  conv_lhs => rw [he,circle_project]
  have hm : J.val/L.val*y∈Ico 0 (0+J.val) := by
    constructor
    · exact mul_nonneg (by positivity) hy.1
    · have hh := mul_lt_mul_of_pos_left hy.2 (by positivity : 0<J.val/L.val)
      have hn : J.val/L.val*L.val=J.val := by field_simp [hLp.ne']
      simpa only [hn,zero_add] using hh
  rw [AddCircle.equivIco_coe_eq hm]
lemma config_representative (N : ℕ) (L J : Length) (X : Configuration N L) :
    representative N J (config N L J X)=(J.val/L.val) • representative N L X := by
  ext i j
  exact circle_representative L J _

lemma circle_distance (L J : Length) (x y : AddCircle L.val) :
    dist (circle L J x) (circle L J y)=J.val/L.val*dist x y := by
  have hLp := L.property
  have hJp := J.property
  rw [dist_eq_norm,←map_sub,dist_eq_norm]
  obtain ⟨z,hz⟩ := QuotientAddGroup.mk_surjective (x-y)
  rw [←hz,circle_project]
  have hj : J.val=J.val/L.val*L.val := by field_simp [hLp.ne']
  have hh := AddCircle.norm_coe_mul L.val z (J.val/L.val)
  rw [←hj,abs_of_pos (by positivity : 0<J.val/L.val)] at hh
  exact hh
lemma torus_distance (L J : Length) (x y : Torus L) :
    torusDistance J (torus L J x) (torus L J y)=(J.val/L.val)*torusDistance L x y := by
  have hLp := L.property
  have hJp := J.property
  unfold torusDistance
  simp only [torus,AddEquiv.piCongrRight_apply,circle_distance,mul_pow,←Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]
lemma config_allowed (N : ℕ) (L J : Length) (a : ℝ) (X : Configuration N L) :
    config N L J X∈allowed N J ((J.val/L.val)*a) ↔ X∈allowed N L a := by
  have hLp := L.property
  have hJp := J.property
  simp only [allowed,mem_ofPred_eq]
  have h : 0<J.val/L.val := by positivity
  simp only [config,AddEquiv.piCongrRight_apply,torus_distance,mul_lt_mul_iff_right₀ h]

lemma volume_config (N : ℕ) (L : Length) :
    (volume : Measure (Configuration N L)) univ=ENNReal.ofReal ((L.val^3)^N) := by
  have hLp := L.property
  rw [show (volume : Measure (Configuration N L))=Measure.pi (fun _ : Fin N ↦ (volume : Measure (Torus L))) from rfl,Measure.pi_univ]
  simp only [BathSlice.volume_torus,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ←ENNReal.ofReal_pow (by positivity : 0≤L.val^3)]

def jacobian (N : ℕ) (L J : Length) : ℝ := (L.val^3/J.val^3)^N
lemma jacobian_pos (N : ℕ) (L J : Length) : 0<jacobian N L J := by
  have hLp := L.property
  have hJp := J.property
  unfold jacobian; positivity
instance config_haar (N : ℕ) (L : Length) : Measure.IsAddHaarMeasure (volume : Measure (Configuration N L)) := by
  let : Measure.IsAddHaarMeasure (volume : Measure (Torus L)) := inferInstance
  exact Measure.pi.isAddHaarMeasure _

lemma config_preserving (N : ℕ) (L J : Length) :
    MeasurePreserving (config N L J) volume (ENNReal.ofReal (jacobian N L J) • volume) := by
  have hLp := L.property
  have hJp := J.property
  let : NeZero (ENNReal.ofReal (jacobian N L J)) := ⟨(ENNReal.ofReal_pos.mpr (jacobian_pos N L J)).ne'⟩
  let : Measure.IsAddHaarMeasure (ENNReal.ofReal (jacobian N L J) • (volume : Measure (Configuration N J))) :=
    Measure.IsAddHaarMeasure.smul _ (ENNReal.ofReal_pos.mpr (jacobian_pos N L J)).ne' ENNReal.ofReal_ne_top
  apply AddMonoidHom.measurePreserving (μ:=(volume : Measure (Configuration N L)))
    (ν:= ENNReal.ofReal (jacobian N L J) • (volume : Measure (Configuration N J))) (f:=(config N L J).toAddMonoidHom) (config_continuous N L J) (config N L J).surjective
  rw [volume_config,Measure.smul_apply,smul_eq_mul,volume_config,
    ←ENNReal.ofReal_mul (jacobian_pos N L J).le]
  congr 1
  unfold jacobian
  rw [div_pow]
  field_simp [hJp.ne']

end Rescaling
end HardSphere
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_PhysicalRescaleLp
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Rescaling
attribute [local instance] Classical.propDecidable

def amplitude (N : ℕ) (L J : Length) : ℝ := Real.sqrt ((jacobian N L J)⁻¹)
lemma amplitude_pos (N : ℕ) (L J : Length) : 0<amplitude N L J :=
  Real.sqrt_pos.mpr (inv_pos.mpr (jacobian_pos N L J))
lemma amplitude_sq (N : ℕ) (L J : Length) : (amplitude N L J)^2=(jacobian N L J)⁻¹ :=
  Real.sq_sqrt (inv_nonneg.mpr (jacobian_pos N L J).le)

def changeMeasure (N : ℕ) (L J : Length) :
    ScalarL2 N J →L[ℝ] Lp ℂ 2 (ENNReal.ofReal (jacobian N L J) • (volume : Measure (Configuration N J))) :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top le_rfl

def rawPull (N : ℕ) (L J : Length) : ScalarL2 N J →L[ℝ] ScalarL2 N L :=
  (Lp.compMeasurePreservingₗᵢ ℝ (config N L J) (config_preserving N L J)).toContinuousLinearMap.comp
    (changeMeasure N L J)

def pull (N : ℕ) (L J : Length) : ScalarL2 N J →L[ℝ] ScalarL2 N L :=
  amplitude N L J • rawPull N L J

lemma rawPull_ae (N : ℕ) (L J : Length) (f : ScalarL2 N J) :
    (rawPull N L J f : Configuration N L → ℂ)=ᵐ[volume] fun X ↦ f (config N L J X) := by
  have ha := Lp.coeFn_compMeasurePreserving (changeMeasure N L J f) (config_preserving N L J)
  have hb := (config_preserving N L J).quasiMeasurePreserving.tendsto_ae.eventually (Lp.coeFn_LpToLpOfMeasureLeSMul
    (E:=ℂ) (p:=2) ENNReal.ofReal_ne_top (le_refl (ENNReal.ofReal (jacobian N L J) • (volume : Measure (Configuration N J)))) f)
  exact ha.trans hb
lemma pull_ae (N : ℕ) (L J : Length) (f : ScalarL2 N J) :
    (pull N L J f : Configuration N L → ℂ)=ᵐ[volume] fun X ↦ amplitude N L J • f (config N L J X) := by
  exact (Lp.coeFn_smul _ _).trans ((rawPull_ae N L J f).fun_comp fun z ↦ amplitude N L J • z)

lemma config_embedding (N : ℕ) (L J : Length) : MeasurableEmbedding (config N L J) :=
  (configHomeo N L J).measurableEmbedding

lemma pull_norm (N : ℕ) (L J : Length) (f : ScalarL2 N J) : ‖pull N L J f‖=‖f‖ := by
  have he : ‖pull N L J f‖^2=‖f‖^2 := by
    rw [scalar_norm_sq_integral]
    calc
      _ = ∫X,‖amplitude N L J • f (config N L J X)‖^2 :=
        integral_congr_ae ((pull_ae N L J f).fun_comp fun z ↦ ‖z‖^2)
      _ = (amplitude N L J)^2 * ∫X,‖f (config N L J X)‖^2 := by
        simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]
      _ = (amplitude N L J)^2 * ((jacobian N L J) * ∫X,‖f X‖^2) := by
        rw [(config_preserving N L J).integral_comp (config_embedding N L J) (fun X ↦ ‖f X‖^2),integral_smul_measure,
          ENNReal.toReal_ofReal (jacobian_pos N L J).le,smul_eq_mul]
      _ = ‖f‖^2 := by rw [amplitude_sq,←mul_assoc,inv_mul_cancel₀ (jacobian_pos N L J).ne',one_mul,←scalar_norm_sq_integral]
  nlinarith [norm_nonneg (pull N L J f),norm_nonneg f]

def jet (N : ℕ) (L J : Length) : Jet N J →L[ℝ] Jet N L :=
  ((pull N L J).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (ContinuousLinearMap.pi fun p ↦ (J.val/L.val) •
      ((pull N L J).comp ((ContinuousLinearMap.proj p).comp (ContinuousLinearMap.snd ℝ _ _))))

end HardSphere.Rescaling
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Rescaling_PhysicalUnitary
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Rescaling

lemma pull_complex_smul (N : ℕ) (L J : Length) (z : ℂ) (f : ScalarL2 N J) :
    pull N L J (z • f)=z • pull N L J f := by
  apply Lp.ext
  have hs := (config_preserving N L J).quasiMeasurePreserving.ae_eq_comp
    (Measure.ae_smul_measure (Lp.coeFn_smul z f) (ENNReal.ofReal (jacobian N L J)))
  filter_upwards [pull_ae N L J (z • f),Lp.coeFn_smul z (pull N L J f),
    pull_ae N L J f,hs] with X h₁ h₂ h₃ h₄
  simp only [Function.comp_apply, Pi.smul_apply] at h₂ h₄
  rw [h₁,h₂,h₃,h₄]
  exact smul_comm _ _ _

lemma circle_inverse (L J : Length) (x : AddCircle L.val) :
    circle J L (circle L J x)=x := by
  obtain ⟨t,ht⟩ := QuotientAddGroup.mk_surjective x
  rw [←ht,circle_project,circle_project]
  congr 1
  field_simp [L.property.ne',J.property.ne']

lemma config_inverse (N : ℕ) (L J : Length) (X : Configuration N L) :
    config N J L (config N L J X)=X := by
  ext i j
  exact circle_inverse L J (X i j)

lemma jacobian_inverse (N : ℕ) (L J : Length) :
    jacobian N L J*jacobian N J L=1 := by
  unfold jacobian
  rw [←mul_pow]
  have h : (L.val^3/J.val^3)*(J.val^3/L.val^3)=(1:ℝ) := by
    field_simp [L.property.ne',J.property.ne']
  rw [h,one_pow]

lemma amplitude_inverse (N : ℕ) (L J : Length) :
    amplitude N L J*amplitude N J L=1 := by
  have h : (amplitude N L J*amplitude N J L)^2=(1:ℝ) := by
    rw [mul_pow,amplitude_sq,amplitude_sq,←mul_inv,jacobian_inverse,inv_one]
  have hp := mul_pos (amplitude_pos N L J) (amplitude_pos N J L)
  nlinarith

lemma pull_inverse (N : ℕ) (L J : Length) (f : ScalarL2 N J) :
    pull N J L (pull N L J f)=f := by
  apply Lp.ext
  have hs := (config_preserving N J L).quasiMeasurePreserving.ae_eq_comp
    (Measure.ae_smul_measure (pull_ae N L J f) (ENNReal.ofReal (jacobian N J L)))
  filter_upwards [pull_ae N J L (pull N L J f),hs] with X h₁ h₂
  simp only [Function.comp_apply] at h₂
  rw [h₁,h₂,config_inverse,smul_smul,amplitude_inverse,one_smul]

def unitary (N : ℕ) (L J : Length) : ScalarL2 N J ≃ₗᵢ[ℂ] ScalarL2 N L where
  toFun := pull N L J
  invFun := pull N J L
  map_add' := (pull N L J).map_add
  map_smul' := pull_complex_smul N L J
  left_inv := pull_inverse N L J
  right_inv := pull_inverse N J L
  norm_map' := pull_norm N L J

@[simp] lemma unitary_apply (N : ℕ) (L J : Length) (f : ScalarL2 N J) :
    unitary N L J f=pull N L J f := rfl

end HardSphere.Rescaling
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_PhysicalRescaleDomain
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Rescaling
attribute [local instance] Classical.propDecidable

lemma coord_pull {N : ℕ} {L J : Length} {a : ℝ} (f : SmoothTest N J a) (c : ℝ)
    (p : Direction N) (X : Configuration N L) :
    coordDerivative N L (fun X ↦ c • f.toFun (config N L J X)) p X=
      (J.val/L.val) • (c • coordDerivative N J f.toFun p (config N L J X)) := by
  let T : LiftedConfiguration N →L[ℝ] LiftedConfiguration N :=
    (J.val/L.val) • ContinuousLinearMap.id ℝ _
  let F := fun Y : LiftedConfiguration N ↦ f.toFun (project N J Y)
  have he : (fun Y : LiftedConfiguration N ↦ c • f.toFun (config N L J (project N L Y)))=
      fun Y ↦ c • F (T Y) := by
    funext Y
    rw [config_project]
    rfl
  have hd := ((((f.smooth.differentiable (by simp)) (T (representative N L X))).hasFDerivAt).comp
    (representative N L X) T.hasFDerivAt).const_smul c
  change HasFDerivAt (fun Y ↦ c • F (T Y)) _ _ at hd
  unfold coordDerivative
  rw [he,hd.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,T,
    ContinuousLinearMap.id_apply,map_smul,←config_representative,smul_smul]
  rw [mul_comm c (J.val/L.val)]

lemma pulled_memLp {N : ℕ} {L J : Length} {f : Configuration N J → ℂ}
    (hf : MemLp f 2 volume) (c : ℝ) :
    MemLp (fun X ↦ c • f (config N L J X)) 2 volume :=
  ((hf.smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving (config_preserving N L J)).const_smul c

def smoothPull {N : ℕ} {L J : Length} {a : ℝ} (f : SmoothTest N J a) :
    SmoothTest N L ((L.val/J.val)*a) where
  toFun X := amplitude N L J • f.toFun (config N L J X)
  smooth := by
    have he : (fun Y : LiftedConfiguration N ↦ amplitude N L J • f.toFun (config N L J (project N L Y)))=
        fun Y ↦ amplitude N L J • f.toFun (project N J ((J.val/L.val) • Y)) := by
      funext Y; rw [config_project]
    rw [he]
    exact (f.smooth.comp (contDiff_id.const_smul (J.val/L.val))).const_smul _
  compact := HasCompactSupport.of_compactSpace _
  support_allowed := by
    intro X hX
    have hs := (tsupport_smul_subset_right (fun _ ↦ amplitude N L J) (f.toFun ∘ config N L J)) hX
    have hc := f.support_allowed ((tsupport_comp_subset_preimage f.toFun (config_continuous N L J)) hs)
    apply (config_allowed N L J ((L.val/J.val)*a) X).mp
    have he : J.val/L.val*((L.val/J.val)*a)=a := by field_simp [L.property.ne',J.property.ne']
    rwa [he]
  memLp := pulled_memLp f.memLp _
  partial_memLp := by
    intro p
    have he : coordDerivative N L (fun X ↦ amplitude N L J • f.toFun (config N L J X)) p=
      fun X ↦ (J.val/L.val) • (amplitude N L J • coordDerivative N J f.toFun p (config N L J X)) :=
        funext (coord_pull f _ p)
    rw [he]
    exact (pulled_memLp (f.partial_memLp p) (amplitude N L J)).const_smul (J.val/L.val)

end HardSphere.Rescaling
end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Rescaling
attribute [local instance] Classical.propDecidable

def torusHomeo (L J : Length) : Torus L ≃ₜ Torus J :=
  Homeomorph.piCongrRight fun _ ↦ AddCircle.homeomorphAddCircle L.val J.val L.property.ne' J.property.ne'

end HardSphere.Rescaling
end
end

end OAI
end


