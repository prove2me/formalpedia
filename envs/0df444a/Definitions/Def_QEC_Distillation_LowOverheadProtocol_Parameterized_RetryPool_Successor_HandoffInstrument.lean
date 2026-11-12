-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_HandoffInstrument
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_HandoffInstrument
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:35:41.661352+00:00
-- url     : https://prove2.me/theorems/8f7282c8-ac4f-4bf7-891c-f48631295761
-- title:
--   Handoff Instrument
-- statement:
--   Definitions and structural lemmas for Handoff Instrument, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/HandoffInstrument.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Semantics_Channels_Instrument
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
abbrev decodedRetryPoolSuccessorHandoffRawIndex {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  Sigma fun _ : decodedRetryPoolRawIndex h hdegree
      (decodedRetryPoolBackwardAttempts m w z q stage)
      (decodedRetryPoolBackwardSchedule m w z q stage) =>
    Fin ((decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage).chosenKrausCount)
abbrev decodedRetryPoolSuccessorHandoffOutcome
    (m w z q : Nat) (stage : Fin z) :=
  Sigma fun _ :
      (Sigma fun _ : tensorPowerHistory DistillationOutcome
        (decodedRetryPoolBackwardAttempts m w z q stage) => PUnit) =>
    PUnit
noncomputable def decodedRetryPoolSuccessorHandoffInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    FiniteInstrument
      (decodedRetryPoolSuccessorHandoffRawIndex h hdegree z q stage hstage)
      (decodedRetryPoolSuccessorHandoffOutcome m w z q stage)
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q stage))
      (decodedRetryPoolSuccessorNestedInputCarrier m w z q stage hstage) :=
  (decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q stage)
      (decodedRetryPoolBackwardSchedule m w z q stage)).bindDependent
    (fun _ => QuantumChannel.toFiniteInstrument
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))
end HH18Parameterized
end Distillation
end QEC


