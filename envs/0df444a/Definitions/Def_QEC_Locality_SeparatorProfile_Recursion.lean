-- Prove2me | Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
-- name    : QEC_Locality_SeparatorProfile_Recursion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:08:08.359421+00:00
-- url     : https://prove2.me/theorems/dd7ecaf8-8246-41be-b2b2-3a6670a17a8a
-- title:
--   Recursion
-- statement:
--   Definitions and structural lemmas for Recursion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_exists_minimumTwoThirdsBalancedVertexSeparator
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
def vertexRestrictedGraph (G : ConnectivityGraph ι) (vertices : Finset ι) :
    ConnectivityGraph ι where
  adjacent x y := x ∈ vertices ∧ y ∈ vertices ∧ G.adjacent x y
  symmetric := by
    rintro x y ⟨hx, hy, hxy⟩
    exact ⟨hy, hx, G.symmetric hxy⟩
  loopless := by
    intro x hxx
    exact G.loopless x hxx.2.2
def edgeRestrictedGraph (G : ConnectivityGraph ι) (edges : Finset (ι × ι)) :
    ConnectivityGraph ι where
  adjacent x y := G.adjacent x y ∧ ((x, y) ∈ edges ∨ (y, x) ∈ edges)
  symmetric := by
    rintro x y ⟨hxy, hmem⟩
    exact ⟨G.symmetric hxy, hmem.symm⟩
  loopless := by
    intro x hxx
    exact G.loopless x hxx.1
theorem left_card_lt_of_twoThirdsPartition
    (G : ConnectivityGraph ι) {vertices left separator right : Finset ι}
    (hvertices : 0 < vertices.card)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right) :
    left.card < vertices.card := by
  have hbalanced : 3 * left.card ≤ 2 * vertices.card := hpartition.2.2.2.1
  omega
theorem right_card_lt_of_twoThirdsPartition
    (G : ConnectivityGraph ι) {vertices left separator right : Finset ι}
    (hvertices : 0 < vertices.card)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right) :
    right.card < vertices.card := by
  have hbalanced : 3 * right.card ≤ 2 * vertices.card := hpartition.2.2.2.2.1
  omega
inductive ProfileSeparatorRecursion (G : ConnectivityGraph ι) (r : Nat) :
    Finset ι → Type u
  | leaf {vertices : Finset ι} (hcard : vertices.card ≤ r) :
      ProfileSeparatorRecursion G r vertices
  | split {vertices left separator right : Finset ι}
      (hpartition :
        TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right)
      (hminimum :
        separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices)
      (hleft : left.card < vertices.card)
      (hright : right.card < vertices.card)
      (leftTree : ProfileSeparatorRecursion G r left)
      (rightTree : ProfileSeparatorRecursion G r right) :
      ProfileSeparatorRecursion G r vertices
structure MinimumSeparatorSplit (G : ConnectivityGraph ι)
    (vertices : Finset ι) where
  left : Finset ι
  separator : Finset ι
  right : Finset ι
  partition :
    TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right
  minimum :
    separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices
noncomputable def chosenMinimumSeparatorSplit
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    MinimumSeparatorSplit G vertices :=
  Classical.choice (by
    rcases exists_minimumTwoThirdsBalancedVertexSeparator G vertices with
      ⟨separator, -, hbalanced, hminimum⟩
    rcases hbalanced with ⟨left, right, hpartition⟩
    exact ⟨⟨left, separator, right, hpartition, hminimum⟩⟩)
noncomputable def buildProfileSeparatorRecursion
    (G : ConnectivityGraph ι) (r : Nat) (hr : 0 < r) (vertices : Finset ι) :
    ProfileSeparatorRecursion G r vertices := by
  classical
  by_cases hleaf : vertices.card ≤ r
  · exact .leaf hleaf
  · let chosen := chosenMinimumSeparatorSplit G vertices
    have hvertices : 0 < vertices.card := by omega
    have hleft := left_card_lt_of_twoThirdsPartition G hvertices chosen.partition
    have hright := right_card_lt_of_twoThirdsPartition G hvertices chosen.partition
    exact .split chosen.partition chosen.minimum hleft hright
      (buildProfileSeparatorRecursion G r hr chosen.left)
      (buildProfileSeparatorRecursion G r hr chosen.right)
termination_by vertices.card
decreasing_by
  · simpa [chosen] using hleft
  · simpa [chosen] using hright
def ProfileSeparatorRecursion.leaves
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι} :
    ProfileSeparatorRecursion G r vertices → List (Finset ι)
  | .leaf _ => if vertices = ∅ then [] else [vertices]
  | .split _ _ _ _ leftTree rightTree => leftTree.leaves ++ rightTree.leaves
def ProfileSeparatorRecursion.leafUnion
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι} :
    ProfileSeparatorRecursion G r vertices → Finset ι
  | .leaf _ => vertices
  | .split _ _ _ _ leftTree rightTree => leftTree.leafUnion ∪ rightTree.leafUnion
def ProfileSeparatorRecursion.separatorUnion
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι} :
    ProfileSeparatorRecursion G r vertices → Finset ι
  | .leaf _ => ∅
  | @split _ _ _ _ _ _ _ separator _ _ _ _ _ leftTree rightTree =>
      separator ∪ leftTree.separatorUnion ∪ rightTree.separatorUnion
def ProfileSeparatorRecursion.root
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι}
    (_ : ProfileSeparatorRecursion G r vertices) : Finset ι :=
  vertices
def ProfileSeparatorRecursion.depth
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι} :
    ProfileSeparatorRecursion G r vertices → Nat
  | .leaf _ => 0
  | .split _ _ _ _ leftTree rightTree =>
      Nat.succ (max leftTree.depth rightTree.depth)
end QEC.Locality


