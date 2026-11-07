-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
-- name    : QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:49:36.865623+00:00
-- url     : https://prove2.me/theorems/99c48b7f-0499-4979-b788-fda81515d40f
-- title:
--   Expansion Probability
-- statement:
--   Definitions and structural lemmas for Expansion Probability, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
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
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
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
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
def ColumnAvoids {r : Nat}
    (S : Finset (Fin (3 * r))) (column : ColumnSample r) : Prop :=
  ∀ a : Fin (3 * r), if a ∈ S then column a = false else True
def ColumnHits {r : Nat}
    (S : Finset (Fin (3 * r))) (column : ColumnSample r) : Prop :=
  ∃ a ∈ S, column a = true
instance instDecidablePredColumnAvoids
    {r : Nat} (S : Finset (Fin (3 * r))) :
    DecidablePred (ColumnAvoids S) := by
  intro column
  unfold ColumnAvoids
  infer_instance
instance instDecidablePredColumnHits
    {r : Nat} (S : Finset (Fin (3 * r))) :
    DecidablePred (ColumnHits S) := by
  intro column
  unfold ColumnHits
  infer_instance
def GroupedExactNeighborhood {r : Nat}
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r)))
    (grouped : GroupedSample r) : Prop :=
  ∀ b : Fin (4 * r),
    if b ∈ T then ColumnHits S (grouped b)
    else ColumnAvoids S (grouped b)
instance instDecidablePredGroupedExactNeighborhood
    {r : Nat} (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    DecidablePred (GroupedExactNeighborhood S T) := by
  intro grouped
  unfold GroupedExactNeighborhood
  infer_instance
instance instDecidablePredExactNeighborhood
    {r : Nat} (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    DecidablePred
      (fun sample : Sample r => checkSetNeighborhood sample S = T) := by
  intro sample
  infer_instance
def SmallNeighborhood (r cutoff : Nat) :=
  {T : Finset (Fin (4 * r)) // T.card ≤ cutoff}
noncomputable instance instFintypeSmallNeighborhood (r cutoff : Nat) :
    Fintype (SmallNeighborhood r cutoff) :=
  Fintype.subtype
    (Finset.univ.filter fun T : Finset (Fin (4 * r)) =>
      T.card ≤ cutoff)
    (by simp)
noncomputable instance instDecidablePredNeighborhoodCardLe
    (r cutoff : Nat) (S : Finset (Fin (3 * r))) :
    DecidablePred
      (fun sample : Sample r =>
        (checkSetNeighborhood sample S).card ≤ cutoff) :=
  Classical.decPred _
def expansionCutoff (Delta : Nat) {r : Nat}
    (S : Finset (Fin (3 * r))) : Nat :=
  (92 * Delta * S.card) / 100
def NonemptyCheckSet (r : Nat) :=
  {S : Finset (Fin (3 * r)) // S.Nonempty}
noncomputable instance instFintypeNonemptyCheckSet (r : Nat) :
    Fintype (NonemptyCheckSet r) :=
  Fintype.subtype
    (Finset.univ.filter fun S : Finset (Fin (3 * r)) => S.Nonempty)
    (by simp)
def SmallNonemptyCheckSet (r Delta : Nat) :=
  {S : NonemptyCheckSet r //
    100000 * Delta * S.1.card ≤ 3 * r}
noncomputable instance instFintypeSmallNonemptyCheckSet
    (r Delta : Nat) :
    Fintype (SmallNonemptyCheckSet r Delta) :=
  Fintype.subtype
    (Finset.univ.filter fun S : NonemptyCheckSet r =>
      100000 * Delta * S.1.card ≤ 3 * r)
    (by simp)
def IsFullyGood {r Delta : Nat} (sample : Sample r) : Prop :=
  IsGood (Delta := Delta) sample ∧
    HasStrongSmallSetExpansion (Delta := Delta) sample
noncomputable instance instDecidablePredIsFullyGood
    (r Delta : Nat) :
    DecidablePred
      (fun sample : Sample r => IsFullyGood (Delta := Delta) sample) :=
  Classical.decPred _
end QEC.Coding.FiberBundle.RandomBase


