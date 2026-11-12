-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageTransition
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageTransition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:38:55.173885+00:00
-- url     : https://prove2.me/theorems/f91d8979-65e2-47c3-864f-5b0409d4bd7b
-- title:
--   Stage Transition
-- statement:
--   Definitions and structural lemmas for Stage Transition, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/StageTransition.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_HandoffInstrument
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
abbrev decodedRetryPoolStageTransitionNextRawHistory {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  tensorPowerHistory
    (decodedRetryPoolRawIndex h hdegree
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
    (logicalOutputCount m w)
abbrev decodedRetryPoolStageTransitionRawIndex {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  Sigma fun _ :
      decodedRetryPoolSuccessorHandoffRawIndex h hdegree z q stage hstage =>
    decodedRetryPoolStageTransitionNextRawHistory h hdegree z q stage hstage
abbrev decodedRetryPoolStageTransitionNextOutcome
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  tensorPowerHistory
    (Sigma fun _ : tensorPowerHistory DistillationOutcome
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) => PUnit)
    (logicalOutputCount m w)
abbrev decodedRetryPoolStageTransitionOutcome
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  Sigma fun _ : decodedRetryPoolSuccessorHandoffOutcome m w z q stage =>
    decodedRetryPoolStageTransitionNextOutcome m w z q stage hstage
abbrev decodedRetryPoolStageTransitionOutputCarrier
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  tensorPowerCarrier
    (Qubit.QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩) ×
        LogicalSite m w))
    (logicalOutputCount m w)
noncomputable def decodedRetryPoolStageTransitionInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    FiniteInstrument
      (decodedRetryPoolStageTransitionRawIndex h hdegree z q stage hstage)
      (decodedRetryPoolStageTransitionOutcome m w z q stage hstage)
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q stage))
      (decodedRetryPoolStageTransitionOutputCarrier m w z q stage hstage) :=
  (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage).bindDependent
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)).tensorPower
          (logicalOutputCount m w))
end HH18Parameterized
end Distillation
end QEC


