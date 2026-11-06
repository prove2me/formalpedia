-- Prove2me | Definitions.Def_QEC_Locality_SeparatorProfile_ExplicitDivision
-- name    : QEC_Locality_SeparatorProfile_ExplicitDivision
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:58:40.582568+00:00
-- url     : https://prove2.me/theorems/17df1e6e-9835-4ded-a816-9378bf29794a
-- title:
--   Explicit Division
-- statement:
--   Definitions and structural lemmas for Explicit Division, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/ExplicitDivision.lean

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedPotential
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_refinedEdgeActive_card_le_uniform_ceil
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_refinedEdgeRegion_incident_card_le
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_refinedEdgeRegions_isEdgeDivision
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_refinedLocalSharedBoundary_card_le
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_directedEdgeFinset_reverseSymmetric
import Theorems.Thm_QEC_Locality_emptyEdgeRegion_isEdgeDivision
import Theorems.Thm_QEC_Locality_profileDivisionRegionConstant_pos
import Theorems.Thm_QEC_Locality_totalEdgeActive_card
import Theorems.Thm_QEC_Locality_totalEdgeRegion_incident_card_le
import Theorems.Thm_QEC_Locality_totalEdgeRegion_isEdgeDivision
import Theorems.Thm_QEC_Locality_totalEdgeRegion_sharedBoundary_eq_empty
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
structure ExplicitProfileEdgeDivision
    (G : ConnectivityGraph ι) (incidentCap localBoundaryCap activeCountCap : Nat) where
  Owner : Type
  [ownerDecidableEq : DecidableEq Owner]
  region : Owner → Finset (ι × ι)
  active : Finset Owner
  isEdgeDivision : IsEdgeDivision G region active
  incident_card_le : ∀ owner, owner ∈ active →
    (edgeIncidentVertices (region owner)).card ≤ incidentCap
  localBoundary_card_le : ∀ owner, owner ∈ active →
    (edgeIncidentVertices (region owner) ∩
      edgeDivisionSharedBoundary region active).card ≤ localBoundaryCap
  active_card_le : active.card ≤ activeCountCap
noncomputable def quantitativeProfileStoppedResult
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : exponent < 1) (r : Nat)
    (hthreshold : profileDivisionThreshold beta exponent ≤ r) :=
  buildQuantitativeStoppedRecursion G beta exponent hProfile hexponent r hthreshold
    (directedEdgeFinset G) Finset.univ subset_rfl
    (directedEdgeFinset_reverseSymmetric G) (Finset.subset_univ _)
noncomputable def quantitativeProfileStoppedTree
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : exponent < 1) (r : Nat)
    (hthreshold : profileDivisionThreshold beta exponent ≤ r) :
    EdgeRestrictedStoppedRecursion G r (directedEdgeFinset G) Finset.univ :=
  (quantitativeProfileStoppedResult G beta exponent hProfile hexponent r hthreshold).1
theorem quantitativeProfileStoppedTree_stoppedAtScale
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : exponent < 1) (r : Nat)
    (hthreshold : profileDivisionThreshold beta exponent ≤ r) :
    (quantitativeProfileStoppedTree G beta exponent hProfile hexponent r hthreshold)
      |>.StoppedAtScale :=
  (quantitativeProfileStoppedResult G beta exponent hProfile hexponent r hthreshold).2
noncomputable def quantitativeProfileEdgeDivision_of_lt
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : 0 < exponent ∧ exponent < 1) (r : Nat)
    (hr : 2 ≤ r) (hthreshold : profileDivisionThreshold beta exponent ≤ r)
    (hrootLarge : r < Fintype.card ι) :
    ExplicitProfileEdgeDivision G r (weightedProfileBoundaryBudget beta exponent r)
      (Nat.ceil (profileDivisionRegionConstant beta exponent * Fintype.card ι / r)) := by
  let tree := quantitativeProfileStoppedTree G beta exponent hProfile hexponent.2 r hthreshold
  have hstopped := quantitativeProfileStoppedTree_stoppedAtScale
    G beta exponent hProfile hexponent.2 r hthreshold
  have hlower : r ≤ 4 * Fintype.card ι := by omega
  exact
    { Owner := tree.refinedOwnerType beta exponent hProfile
      region := tree.refinedEdgeRegion beta exponent hProfile
      active := tree.refinedEdgeActive beta exponent hProfile
      isEdgeDivision := tree.refinedEdgeRegions_isEdgeDivision beta exponent hProfile rfl
      incident_card_le := fun owner _ =>
        tree.refinedEdgeRegion_incident_card_le beta exponent hProfile owner
      localBoundary_card_le := fun owner _ => by
        simpa [weightedProfileBoundaryBudget] using
          tree.refinedLocalSharedBoundary_card_le beta exponent hProfile owner
      active_card_le := tree.refinedEdgeActive_card_le_uniform_ceil hstopped beta exponent
        hProfile hexponent (by omega) hthreshold hlower }
noncomputable def emptyProfileEdgeDivision
    (G : ConnectivityGraph ι) (hedgeless : directedEdgeFinset G = ∅)
    (incidentCap localBoundaryCap activeCountCap : Nat) :
    ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap :=
  { Owner := Unit
    region := emptyEdgeRegion
    active := emptyEdgeActive
    isEdgeDivision := emptyEdgeRegion_isEdgeDivision G hedgeless
    incident_card_le := by simp [emptyEdgeActive]
    localBoundary_card_le := by simp [emptyEdgeActive]
    active_card_le := by simp [emptyEdgeActive] }
omit [DecidableEq ι] in
/-- A nonempty edge set certifies that the ambient finite vertex type is nonempty. -/
theorem vertexCount_pos_of_directedEdges_nonempty
    (G : ConnectivityGraph ι) (hedges : (directedEdgeFinset G).Nonempty) :
    0 < Fintype.card ι := by
  rcases hedges with ⟨⟨x, y⟩, hxy⟩
  exact Fintype.card_pos_iff.mpr ⟨x⟩
noncomputable def totalProfileEdgeDivision
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hbeta : 1 ≤ beta) (hexponent : 0 < exponent ∧ exponent < 1)
    (r : Nat) (hr : 2 ≤ r) (hcard : Fintype.card ι ≤ r)
    (hedges : (directedEdgeFinset G).Nonempty) :
    ExplicitProfileEdgeDivision G r (weightedProfileBoundaryBudget beta exponent r)
      (Nat.ceil (profileDivisionRegionConstant beta exponent * Fintype.card ι / r)) := by
  have hcountPositive : 0 <
      profileDivisionRegionConstant beta exponent * Fintype.card ι / r := by
    exact div_pos
      (mul_pos (profileDivisionRegionConstant_pos hbeta hexponent)
        (by exact_mod_cast vertexCount_pos_of_directedEdges_nonempty G hedges))
      (by exact_mod_cast (show 0 < r by omega))
  exact
    { Owner := Unit
      region := totalEdgeRegion G
      active := totalEdgeActive
      isEdgeDivision := totalEdgeRegion_isEdgeDivision G
      incident_card_le := by
        intro owner _
        simpa [show owner = () from Subsingleton.elim _ _] using
          totalEdgeRegion_incident_card_le G hcard
      localBoundary_card_le := by
        intro owner _
        have hempty := totalEdgeRegion_sharedBoundary_eq_empty G
        simp [hempty]
      active_card_le := by
        rw [totalEdgeActive_card]
        exact Nat.one_le_ceil_iff.mpr hcountPositive }
noncomputable def explicitProfileEdgeDivision
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : 0 < exponent ∧ exponent < 1) (r : Nat)
    (hr : 2 ≤ r) (hthreshold : profileDivisionThreshold beta exponent ≤ r) :
    ExplicitProfileEdgeDivision G r (weightedProfileBoundaryBudget beta exponent r)
      (Nat.ceil (profileDivisionRegionConstant beta exponent * Fintype.card ι / r)) := by
  classical
  by_cases hedgeless : directedEdgeFinset G = ∅
  · exact emptyProfileEdgeDivision G hedgeless _ _ _
  · have hedges : (directedEdgeFinset G).Nonempty := Finset.nonempty_iff_ne_empty.mpr hedgeless
    by_cases hcard : Fintype.card ι ≤ r
    · exact totalProfileEdgeDivision G beta exponent hProfile.1 hexponent r hr hcard hedges
    · exact quantitativeProfileEdgeDivision_of_lt G beta exponent hProfile hexponent r hr
        hthreshold (Nat.lt_of_not_ge hcard)
end QEC.Locality


