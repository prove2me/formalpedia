-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_NestedSuccessorStage
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_NestedSuccessorStage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:48:36.66545+00:00
-- url     : https://prove2.me/theorems/4b7a4755-55bf-428d-bf4c-c93080b3c985
-- title:
--   Nested Successor Stage
-- statement:
--   Definitions and structural lemmas for Nested Successor Stage, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/NestedSuccessorStage.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageTransition
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
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
abbrev decodedRetryPoolSuccessorStageRawIndex {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  Sigma fun _ : Fin
      ((decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage).chosenKrausCount) =>
    tensorPowerHistory
      (decodedRetryPoolRawIndex h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
      (logicalOutputCount m w)
abbrev decodedRetryPoolSuccessorStageOutcome
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  Sigma fun _ : PUnit =>
    tensorPowerHistory
      (Sigma fun _ : tensorPowerHistory DistillationOutcome
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) => PUnit)
      (logicalOutputCount m w)
noncomputable def decodedRetryPoolSuccessorStageInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    FiniteInstrument
      (decodedRetryPoolSuccessorStageRawIndex h hdegree z q stage hstage)
      (decodedRetryPoolSuccessorStageOutcome m w z q stage hstage)
      (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
      (tensorPowerCarrier
        (QubitRegister
          (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩) ×
            LogicalSite m w))
        (logicalOutputCount m w)) :=
  (QuantumChannel.toFiniteInstrument
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage)).bindDependent
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)).tensorPower
          (logicalOutputCount m w))
noncomputable def decodedRetryPoolNestedSuccessorStageInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    FiniteInstrument
      (nestedTensorHistory
        (decodedRetryPoolSuccessorStageRawIndex h hdegree z q stage hstage)
        (logicalOutputCount m w) stage.1)
      (nestedTensorHistory
        (decodedRetryPoolSuccessorStageOutcome m w z q stage hstage)
        (logicalOutputCount m w) stage.1)
      (nestedTensorCarrier
        (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
        (logicalOutputCount m w) stage.1)
      (nestedTensorCarrier
        (QubitRegister
          (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩) ×
            LogicalSite m w))
        (logicalOutputCount m w) (stage.1 + 1)) :=
  nestedTensorPower
    (decodedRetryPoolSuccessorStageInstrument h hdegree z q stage hstage)
    (logicalOutputCount m w) stage.1
end HH18Parameterized
end Distillation
end QEC


