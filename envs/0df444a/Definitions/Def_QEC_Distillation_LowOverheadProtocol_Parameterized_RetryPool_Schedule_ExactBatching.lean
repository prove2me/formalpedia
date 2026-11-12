-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T20:08:45.413591+00:00
-- url     : https://prove2.me/theorems/4349e2e7-b71b-4fac-af64-a9fe71d0b7c0
-- title:
--   Exact Batching
-- statement:
--   Definitions and structural lemmas for Exact Batching, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
def decodedRetryPoolExactBatchTerminalRequest : Nat → Nat
  | 0 => 1
  | z + 1 =>
      (decodedRetryPoolDyadicDenominator z - 1) *
        decodedRetryPoolExactBatchTerminalRequest z
def decodedRetryPoolExactBatchDenominatorProduct : Nat → Nat
  | 0 => 1
  | z + 1 =>
      decodedRetryPoolDyadicDenominator z *
        decodedRetryPoolExactBatchDenominatorProduct z
end QEC.Distillation.HH18Parameterized


