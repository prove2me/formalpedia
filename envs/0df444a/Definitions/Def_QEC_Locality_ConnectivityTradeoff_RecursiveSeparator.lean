-- Prove2me | Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
-- name    : QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:03:00.229249+00:00
-- url     : https://prove2.me/theorems/ab055f16-1c29-44ee-8e00-26f0f49fad89
-- title:
--   Recursive Separator
-- statement:
--   Definitions and structural lemmas for Recursive Separator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
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
noncomputable section
namespace QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
noncomputable def measuredTwoThirdsSeparator
    (G : ConnectivityGraph ι) (vertices : Finset ι) : Finset ι :=
  Classical.choose (exists_minimumTwoThirdsBalancedVertexSeparator G vertices)
theorem measuredTwoThirdsSeparator_spec
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    measuredTwoThirdsSeparator G vertices ⊆ vertices ∧
      IsTwoThirdsBalancedVertexSeparator G vertices
        (measuredTwoThirdsSeparator G vertices) ∧
      (measuredTwoThirdsSeparator G vertices).card =
        minimumTwoThirdsBalancedVertexSeparatorSize G vertices :=
  Classical.choose_spec (exists_minimumTwoThirdsBalancedVertexSeparator G vertices)
noncomputable def measuredTwoThirdsLeft
    (G : ConnectivityGraph ι) (vertices : Finset ι) : Finset ι :=
  Classical.choose (measuredTwoThirdsSeparator_spec G vertices).2.1
noncomputable def measuredTwoThirdsRight
    (G : ConnectivityGraph ι) (vertices : Finset ι) : Finset ι :=
  Classical.choose (Classical.choose_spec
    (measuredTwoThirdsSeparator_spec G vertices).2.1)
theorem measuredTwoThirdsSplit_spec
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    TwoThirdsBalancedPartitionAfterDeleting G vertices
      (measuredTwoThirdsLeft G vertices)
      (measuredTwoThirdsSeparator G vertices)
      (measuredTwoThirdsRight G vertices) :=
  Classical.choose_spec (Classical.choose_spec
    (measuredTwoThirdsSeparator_spec G vertices).2.1)
theorem measuredTwoThirdsLeft_card_lt
    (G : ConnectivityGraph ι) (vertices : Finset ι) (hvertices : vertices.Nonempty) :
    (measuredTwoThirdsLeft G vertices).card < vertices.card := by
  have hbalance := (measuredTwoThirdsSplit_spec G vertices).2.2.2.1
  have hpositive : 0 < vertices.card := Finset.card_pos.mpr hvertices
  omega
theorem measuredTwoThirdsRight_card_lt
    (G : ConnectivityGraph ι) (vertices : Finset ι) (hvertices : vertices.Nonempty) :
    (measuredTwoThirdsRight G vertices).card < vertices.card := by
  have hbalance := (measuredTwoThirdsSplit_spec G vertices).2.2.2.2.1
  have hpositive : 0 < vertices.card := Finset.card_pos.mpr hvertices
  omega
def bkSeparatorTerminal (d : Nat) (vertices : Finset ι) : Prop :=
  vertices = ∅ ∨ vertices.card < d
noncomputable def bkSeparatorRecurrence
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι) : Nat := by
  classical
  exact if bkSeparatorTerminal d vertices then 0
    else
      twoThirdsSeparationProfile G vertices.card +
        bkSeparatorRecurrence G d (measuredTwoThirdsLeft G vertices) +
        bkSeparatorRecurrence G d (measuredTwoThirdsRight G vertices)
termination_by vertices.card
decreasing_by
  all_goals
    have hnonempty : vertices.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      apply ‹¬bkSeparatorTerminal d vertices›
      exact Or.inl hempty
    first
    | exact measuredTwoThirdsLeft_card_lt G vertices hnonempty
    | exact measuredTwoThirdsRight_card_lt G vertices hnonempty
def bkScaleTerminal (d r : Nat) : Prop :=
  r = 0 ∨ r < d
def bkTwoThirdsChildScale (r : Nat) : Nat :=
  2 * r / 3
theorem bkTwoThirdsChildScale_lt (r : Nat) (hr : 0 < r) :
    bkTwoThirdsChildScale r < r := by
  simp only [bkTwoThirdsChildScale]
  omega
noncomputable def bkScaleRecurrence
    (G : ConnectivityGraph ι) (d r : Nat) : Nat := by
  classical
  exact if bkScaleTerminal d r then 0
    else
      twoThirdsSeparationProfile G r +
        bkScaleRecurrence G d (bkTwoThirdsChildScale r) +
        bkScaleRecurrence G d (bkTwoThirdsChildScale r)
termination_by r
decreasing_by
  all_goals
    apply bkTwoThirdsChildScale_lt
    by_contra hr
    apply ‹¬bkScaleTerminal d r›
    exact Or.inl (Nat.eq_zero_of_not_pos hr)
structure BKRecursivePartition
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι) where
  pieces : Finset (Finset ι)
  remainder : Finset ι
  piece_subset : ∀ piece, piece ∈ pieces → piece ⊆ vertices
  remainder_subset : remainder ⊆ vertices
  covers : pieces.biUnion id ∪ remainder = vertices
  pieces_remainder_disjoint : Disjoint (pieces.biUnion id) remainder
  piece_card_lt : ∀ piece, piece ∈ pieces → piece.card < d
  pairwise_decoupled : ∀ left, left ∈ pieces → ∀ right, right ∈ pieces → left ≠ right →
    Disjoint left right ∧ NoEdgeBetween G left right
  remainder_card_le : remainder.card ≤ bkSeparatorRecurrence G d vertices
def bkScaleRecurrenceTwice (G : ConnectivityGraph ι) (d r : Nat) : Nat :=
  bkScaleRecurrence G d (bkScaleRecurrence G d r)
end QEC.Locality
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open QEC Semantics Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation


