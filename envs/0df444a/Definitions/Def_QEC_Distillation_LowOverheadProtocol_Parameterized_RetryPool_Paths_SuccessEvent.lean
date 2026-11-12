-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T20:02:54.212342+00:00
-- url     : https://prove2.me/theorems/aa0cbf3a-6424-42a0-af78-eb046b2a8b45
-- title:
--   Success Event
-- statement:
--   Definitions and structural lemmas for Success Event, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/SuccessEvent.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_NestedPathRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_SelectedEnoughBranch
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
def decodedRetryPoolProtocolPathSuccessfulRoutingAux
    (m w z q : Nat) : (stage : Nat) -> (hstage : stage < z) ->
      routedDepthOutputSlots m w stage ->
      decodedRetryPoolProtocolOutcomeAux m w z q stage hstage -> Bool
  | 0, hzero, _, outcome =>
      decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hzero⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hzero⟩) outcome
  | stage + 1, hstage, path, outcome =>
      let priorPath := routedDepthOutputPathInit m w stage path
      let port := routedDepthOutputPathLast m w stage path
      let nestedPath :=
        (decodedRetryPoolNestedPathEquiv m w stage).symm priorPath
      let successorOutcome :=
        nestedTensorHistoryAt
          (decodedRetryPoolSuccessorStageOutcome
            m w z q ⟨stage, by omega⟩ hstage)
          (logicalOutputCount m w) stage outcome.2 nestedPath
      decodedRetryPoolProtocolPathSuccessfulRoutingAux
          m w z q stage (by omega) priorPath outcome.1 &&
        decodedRetryPoolSuccessorStageSelectedPoolEnough
          m w z q ⟨stage, by omega⟩ hstage port successorOutcome
end HH18Parameterized
end Distillation
end QEC


