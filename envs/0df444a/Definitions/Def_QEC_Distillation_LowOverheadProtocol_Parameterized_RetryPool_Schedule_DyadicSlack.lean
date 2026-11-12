-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:04:38.192911+00:00
-- url     : https://prove2.me/theorems/b06c3598-c388-4aba-8146-47d6770c0f3b
-- title:
--   Dyadic Slack
-- statement:
--   Definitions and structural lemmas for Dyadic Slack, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/DyadicSlack.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_FirstMoment
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
local instance instDecodedRetryPoolDyadicSlackClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
def decodedRetryPoolDyadicDenominator (stage : Nat) : Nat :=
  2 ^ (stage + 3)
def decodedRetryPoolCeilDiv (numerator denominator : Nat) : Nat :=
  (numerator + denominator - 1) / denominator
def decodedRetryPoolDyadicAttempts (stage required : Nat) : Nat :=
  decodedRetryPoolCeilDiv
    (decodedRetryPoolDyadicDenominator stage * required)
    (decodedRetryPoolDyadicDenominator stage - 1)
end HH18Parameterized
end Distillation
end QEC


