-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T20:06:12.163774+00:00
-- url     : https://prove2.me/theorems/6045cb81-c1d8-4393-9f45-2459f68bad4b
-- title:
--   Branch Operator
-- statement:
--   Definitions and structural lemmas for Branch Operator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
noncomputable def decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage < z)
    (path : routedDepthOutputSlots m w stage)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨stage, hstage⟩) ×
        LogicalSite m w)) :=
  nestedTensorCoordinateOperator
    (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨stage, hstage⟩) ×
        LogicalSite m w))
    (logicalOutputCount m w) stage
    ((decodedRetryPoolNestedPathEquiv m w stage).symm path)
    (∑ outcome : decodedRetryPoolProtocolOutcomeAux m w z q stage hstage,
      if decodedRetryPoolProtocolPathSuccessfulRoutingAux
          m w z q stage hstage path outcome = true then
        (decodedRetryPoolProtocolInstrumentAux
          h hdegree z q hz stage hstage).branchOperator outcome rho.toOperator
      else 0)
noncomputable def decodedRetryPoolProtocolPathEnoughMassAux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (stage : Nat) -> (hstage : stage < z) ->
      routedDepthOutputSlots m w stage -> Real
  | 0, hzero, _ =>
      decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hzero⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hzero⟩)
        (decodedRetryPoolPhysicalProtocolNoisyRootInput
          m w z q hzero epsilon rhoUnit)
  | stage + 1, hstage, path =>
      let priorPath := routedDepthOutputPathInit m w stage path
      let port := routedDepthOutputPathLast m w stage path
      let priorRate :=
        routedDepthPathRate h hdegree epsilon hsmall stage priorPath
      let hhalf :=
        routedDepthPathNextHalf h hdegree epsilon hsmall priorPath port
      decodedRetryPoolProtocolPathEnoughMassAux
          h hdegree epsilon hsmall z q rhoUnit stage (by omega) priorPath *
        decodedRetryPoolEnoughMass h hdegree
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage + 1, hstage⟩)
          (decodedRetryPoolSuccessorStageSelectedNextInput
            h hdegree priorRate z q ⟨stage, by omega⟩ hstage port hhalf
            rhoUnit)
noncomputable def decodedRetryPoolProtocolPathSuccessorEnoughOperator
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q stage : Nat) (hstage : stage + 1 < z)
    (port : LogicalSite m w)
    (A : Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage, by omega⟩) × LogicalSite m w))) :
    Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage + 1, hstage⟩) × LogicalSite m w)) :=
  tensorPowerCoordinateOperator (logicalOutputCount m w)
    (decodedRetryPoolLogicalSiteFinEquiv m w port)
    (∑ successorOutcome : decodedRetryPoolSuccessorStageOutcome
        m w z q ⟨stage, by omega⟩ hstage,
      if decodedRetryPoolSuccessorStageSelectedPoolEnough
          m w z q ⟨stage, by omega⟩ hstage port successorOutcome = true then
        (decodedRetryPoolSuccessorStageInstrument
          h hdegree z q ⟨stage, by omega⟩ hstage).branchOperator
            successorOutcome A
      else 0)
noncomputable def decodedRetryPoolProtocolRootSuccessfulBranchOperator
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩) ×
        LogicalSite m w)) :=
  ∑ outcome : decodedRetryPoolProtocolOutcomeAux m w z q 0 hz,
    if decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩)
        outcome = true then
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩)).branchOperator
          outcome rho.toOperator
    else 0
noncomputable def decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    (stage : Nat) -> (hstage : stage < z) ->
      routedDepthOutputSlots m w stage ->
      Operator (QubitRegister
        (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨stage, hstage⟩) ×
          LogicalSite m w))
  | 0, hzero, _ =>
      decodedRetryPoolProtocolRootSuccessfulBranchOperator
        h hdegree z q hzero rho
  | stage + 1, hstage, path =>
      decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q stage hstage
          (routedDepthOutputPathLast m w stage path)
          (decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
            h hdegree z q hz rho stage (by omega)
              (routedDepthOutputPathInit m w stage path))
end HH18Parameterized
end Distillation
end QEC


