-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T20:06:21.789654+00:00
-- url     : https://prove2.me/theorems/d6413a10-7662-4797-b3dd-77c463595471
-- title:
--   Schedule Bridge
-- statement:
--   Definitions and structural lemmas for Schedule Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
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
abbrev decodedRetryPoolPhysicalProtocolRootInputSlots
    (m w z q : Nat) (hz : 0 < z) :=
  decodedRetryPoolBackwardRootRawCarrier m w z q hz
abbrev decodedRetryPoolPhysicalProtocolTerminalOutputSlots
    (m w z q : Nat) :=
  decodedRetryPoolBackwardTerminalGoodCarrier m w z q
end HH18Parameterized
end Distillation
end QEC


