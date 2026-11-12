-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:55:24.153189+00:00
-- url     : https://prove2.me/theorems/8aa59dbd-594f-4509-a711-f0b5252081af
-- title:
--   Success Event
-- statement:
--   Definitions and structural lemmas for Success Event, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessEvent.lean

import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
def tensorPowerHistoryAll {alpha : Type*} (predicate : alpha -> Bool) :
    (attempts : Nat) -> tensorPowerHistory alpha attempts -> Bool
  | 0, _ => true
  | attempts + 1, history =>
      predicate history.1 && tensorPowerHistoryAll predicate attempts history.2
def nestedTensorHistoryAll {alpha : Type*} (predicate : alpha -> Bool)
    (branches : Nat) : (depth : Nat) -> nestedTensorHistory alpha branches depth -> Bool
  | 0, outcome => predicate outcome
  | depth + 1, history =>
      nestedTensorHistoryAll
        (fun layer => tensorPowerHistoryAll predicate branches layer)
        branches depth history
def decodedRetryPoolOutcomeEnough (attempts required : Nat)
    (outcome : Sigma fun _ : tensorPowerHistory DistillationOutcome attempts => PUnit) : Bool :=
  decide (required <=
    (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts outcome.1).card)
def decodedRetryPoolSuccessorStageRoutingGood
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (outcome : decodedRetryPoolSuccessorStageOutcome m w z q stage hstage) : Bool :=
  tensorPowerHistoryAll
    (decodedRetryPoolOutcomeEnough
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
    (logicalOutputCount m w) outcome.2
def decodedRetryPoolProtocolSuccessfulRoutingAux
    (m w z q : Nat) : (stage : Nat) -> (hstage : stage < z) ->
      decodedRetryPoolProtocolOutcomeAux m w z q stage hstage -> Bool
  | 0, hzero, outcome =>
      decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hzero⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hzero⟩) outcome
  | stage + 1, hstage, outcome =>
      let previous : Fin z := ⟨stage, by omega⟩
      decodedRetryPoolProtocolSuccessfulRoutingAux
          m w z q stage (by omega) outcome.1 &&
        nestedTensorHistoryAll
          (decodedRetryPoolSuccessorStageRoutingGood
            m w z q previous hstage)
          (logicalOutputCount m w) stage outcome.2
def decodedRetryPoolPhysicalProtocolSuccessfulRouting
    (m w z q : Nat) (hz : 0 < z)
    (outcome : decodedRetryPoolPhysicalProtocolOutcome m w z q hz) : Bool :=
  decodedRetryPoolProtocolSuccessfulRoutingAux
    m w z q (z - 1) (by omega) outcome
noncomputable def decodedRetryPoolPhysicalProtocolBinaryInstrument
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) :=
  (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz).binaryCoarsen
    (decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz)
noncomputable def decodedRetryPoolPhysicalProtocolSuccessMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) : Real :=
  (decodedRetryPoolPhysicalProtocolBinaryInstrument
    h hdegree z q hz).bornWeight .accepted rho
end HH18Parameterized
end Distillation
end QEC


