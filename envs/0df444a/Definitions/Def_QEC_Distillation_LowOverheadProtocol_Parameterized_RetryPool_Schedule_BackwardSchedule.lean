-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:06:43.041412+00:00
-- url     : https://prove2.me/theorems/7e668f99-29ed-405d-83e2-93a3af3eb74b
-- title:
--   Backward Schedule
-- statement:
--   Definitions and structural lemmas for Backward Schedule, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
set_option autoImplicit false
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
attribute [local instance 100] Fintype.ofFinite
def decodedRetryPoolBackwardRequiredAtDistance (m w z q : Nat) : Nat → Nat
  | 0 => q
  | distance + 1 =>
      physicalInputCount m w *
        decodedRetryPoolDyadicAttempts (z - (distance + 1))
          (decodedRetryPoolBackwardRequiredAtDistance m w z q distance)
def decodedRetryPoolBackwardSchedule (m w z q : Nat) (stage : Fin z) : Nat :=
  decodedRetryPoolBackwardRequiredAtDistance m w z q (z - 1 - stage.1)
def decodedRetryPoolBackwardAttempts (m w z q : Nat) (stage : Fin z) : Nat :=
  decodedRetryPoolDyadicAttempts stage.1
    (decodedRetryPoolBackwardSchedule m w z q stage)
abbrev decodedRetryPoolBackwardRootRawCarrier (m w z q : Nat) (hz : 0 < z) :=
  Fin (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) × PhysicalSite m w
abbrev decodedRetryPoolBackwardTerminalGoodCarrier (m w z q : Nat) :=
  Fin q × (Fin z → LogicalSite m w)
end HH18Parameterized
end Distillation
end QEC


