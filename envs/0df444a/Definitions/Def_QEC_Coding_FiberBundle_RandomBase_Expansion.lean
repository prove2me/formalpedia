-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
-- name    : QEC_Coding_FiberBundle_RandomBase_Expansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:36:46.688374+00:00
-- url     : https://prove2.me/theorems/2dfdeb8c-d82c-4f54-8b10-62c90370269b
-- title:
--   Expansion
-- statement:
--   Definitions and structural lemmas for Expansion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
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
def selectedCheckCount
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) (b : Fin (4 * r)) : Nat :=
  (S.filter fun a => sample (a, b)).card
def checkSetNeighborhood
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) : Finset (Fin (4 * r)) :=
  Finset.univ.filter fun b => 0 < selectedCheckCount sample S b
def couniqueNeighbors
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) : Finset (Fin (4 * r)) :=
  Finset.univ.filter fun b => selectedCheckCount sample S b = 1
def nonCouniqueNeighbors
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) : Finset (Fin (4 * r)) :=
  Finset.univ.filter fun b => 2 ≤ selectedCheckCount sample S b
def selectedIncidenceCount
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) : Nat :=
  ∑ a ∈ S, checkDegree sample a
def HasStrongSmallSetExpansion
    {r Delta : Nat} (sample : Sample r) : Prop :=
  ∀ S : Finset (Fin (3 * r)),
    100000 * Delta * S.card ≤ 3 * r →
      92 * Delta * S.card ≤
        100 * (checkSetNeighborhood sample S).card
def couniqueDegree
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) (a : Fin (3 * r)) : Nat :=
  ((couniqueNeighbors sample S).filter fun b => sample (a, b)).card
def AvoidsOutside
    {r : Nat} (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) (sample : Sample r) : Prop :=
  ∀ edge : Fin (3 * r) × Fin (4 * r),
    if edge.1 ∈ S ∧ edge.2 ∉ T then sample edge = false else True
instance instDecidablePredAvoidsOutside
    {r : Nat} (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    DecidablePred (AvoidsOutside S T) := by
  intro sample
  unfold AvoidsOutside
  infer_instance
def ExpansionWitness (r Delta : Nat) :=
  {pair :
      Finset (Fin (3 * r)) × Finset (Fin (4 * r)) //
    100000 * Delta * pair.1.card ≤ 3 * r ∧
      100 * pair.2.card < 92 * Delta * pair.1.card}
noncomputable instance instFintypeExpansionWitness (r Delta : Nat) :
    Fintype (ExpansionWitness r Delta) :=
  Fintype.subtype
    (Finset.univ.filter fun pair :
      Finset (Fin (3 * r)) × Finset (Fin (4 * r)) =>
        100000 * Delta * pair.1.card ≤ 3 * r ∧
          100 * pair.2.card < 92 * Delta * pair.1.card)
    (by simp)
noncomputable instance instDecidablePredHasStrongSmallSetExpansion
    (r Delta : Nat) :
    DecidablePred
      (fun sample : Sample r =>
        HasStrongSmallSetExpansion (Delta := Delta) sample) :=
  Classical.decPred _
end QEC.Coding.FiberBundle.RandomBase


