-- Prove2me | Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
-- name    : QEC_Distillation_TwoQubitOperations_ParityWeights
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:22:09.915182+00:00
-- url     : https://prove2.me/theorems/94f36b06-8c1c-4d96-8aa4-e694b0d37f28
-- title:
--   Parity Weights
-- statement:
--   Definitions and structural lemmas for Parity Weights, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityWeights.lean

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace TwoQubit
open scoped InnerProductSpace
def zzEvenWeight (psi : TwoQubitSpace) : ℝ :=
  ‖zzEvenProjector psi‖ ^ 2
def zzOddWeight (psi : TwoQubitSpace) : ℝ :=
  ‖zzOddProjector psi‖ ^ 2
end TwoQubit
end Distillation
end QEC


