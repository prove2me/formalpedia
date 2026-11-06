-- Prove2me | Definitions.Def_QEC_Locality_SeparatorProfile_Completion
-- name    : QEC_Locality_SeparatorProfile_Completion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:46:45.184505+00:00
-- url     : https://prove2.me/theorems/5e4001a5-1743-4532-8f33-4c7668e5379c
-- title:
--   Completion
-- statement:
--   Definitions and structural lemmas for Completion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Completion.lean

import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_reverse
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_subset
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeRegion_reverse
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeRegion_subset
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
namespace QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
noncomputable def EdgeRestrictedStoppedRecursion.terminalCarrier
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) →
      tree.edgeOwnerType → Finset ι
  | .leaf (vertices := vertices) _ _ _ _, _ => vertices
  | .split _ _ _ _ _ _ _ leftTree rightTree, owner =>
      match owner with
      | Sum.inl owner => leftTree.terminalCarrier owner
      | Sum.inr owner => rightTree.terminalCarrier owner
noncomputable def EdgeRestrictedStoppedRecursion.terminalBoundary
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) : Finset ι :=
  tree.edgeOwnerAncestors owner ∩ edgeIncidentVertices (tree.edgeRegion owner)
theorem EdgeRestrictedStoppedRecursion.rootEdges_subset_directed
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) :
    edges ⊆ directedEdgeFinset G := by
  cases tree with
  | leaf hsubset _ _ _ => exact hsubset
  | split hsubset _ _ _ _ _ _ _ _ => exact hsubset
theorem EdgeRestrictedStoppedRecursion.terminal_incident_subset_carrier
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) :
    edgeIncidentVertices (tree.edgeRegion owner) ⊆ tree.terminalCarrier owner := by
  induction tree with
  | leaf _ _ hincident _ => simpa [edgeRegion, terminalCarrier] using hincident
  | split _ _ _ _ _ _ _ leftTree rightTree ihLeft ihRight =>
      cases owner with
      | inl owner => exact ihLeft owner
      | inr owner => exact ihRight owner
theorem EdgeRestrictedStoppedRecursion.terminalCarrier_card_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) :
    (tree.terminalCarrier owner).card ≤ r := by
  induction tree with
  | leaf _ _ _ hcard => simpa [terminalCarrier] using hcard
  | split _ _ _ _ _ _ _ leftTree rightTree ihLeft ihRight =>
      cases owner with
      | inl owner => exact ihLeft owner
      | inr owner => exact ihRight owner
theorem EdgeRestrictedStoppedRecursion.terminalBoundary_subset_carrier
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) :
    tree.terminalBoundary owner ⊆ tree.terminalCarrier owner :=
  Finset.inter_subset_right.trans (tree.terminal_incident_subset_carrier owner)
noncomputable def EdgeRestrictedStoppedRecursion.weightedRefinementAt
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.edgeOwnerType) :
    WeightedBoundaryEdgeRecursion G r (weightedSpineSeparatorBudget beta exponent r)
      (tree.edgeRegion owner) (tree.terminalCarrier owner) (tree.terminalBoundary owner) :=
  buildWeightedBoundaryEdgeRecursion G beta exponent hProfile r
    (tree.edgeRegion owner) (tree.terminalCarrier owner) (tree.terminalBoundary owner)
    ((tree.edgeRegion_subset owner).trans tree.rootEdges_subset_directed)
    (tree.edgeRegion_reverse owner)
    (tree.terminal_incident_subset_carrier owner)
    (tree.terminalBoundary_subset_carrier owner)
    (tree.terminalCarrier_card_le owner)
def EdgeRestrictedStoppedRecursion.refinedOwnerType
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent) : Type :=
  Sigma fun owner : tree.edgeOwnerType =>
    (tree.weightedRefinementAt beta exponent hProfile owner).edgeOwnerType
noncomputable instance EdgeRestrictedStoppedRecursion.refinedOwnerFintype
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent) :
    Fintype (tree.refinedOwnerType beta exponent hProfile) := by
  unfold refinedOwnerType
  infer_instance
noncomputable instance EdgeRestrictedStoppedRecursion.refinedOwnerDecidableEq
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent) :
    DecidableEq (tree.refinedOwnerType beta exponent hProfile) := by
  unfold refinedOwnerType
  infer_instance
noncomputable def EdgeRestrictedStoppedRecursion.refinedEdgeRegion
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) : Finset (ι × ι) :=
  (tree.weightedRefinementAt beta exponent hProfile owner.1).edgeRegion owner.2
noncomputable def EdgeRestrictedStoppedRecursion.refinedEdgeActive
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent) :
    Finset (tree.refinedOwnerType beta exponent hProfile) := by
  classical
  exact Finset.univ.filter fun owner =>
    (tree.refinedEdgeRegion beta exponent hProfile owner).Nonempty
noncomputable def EdgeRestrictedStoppedRecursion.refinedOwnerBoundary
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) : Finset ι :=
  (tree.weightedRefinementAt beta exponent hProfile owner.1).ownerBoundary owner.2
noncomputable def EdgeRestrictedStoppedRecursion.terminalBoundaryMass
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) : Nat :=
  ∑ owner : tree.edgeOwnerType, (tree.terminalBoundary owner).card
end QEC.Locality


