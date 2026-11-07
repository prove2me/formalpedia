-- Prove2me | Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
-- name    : QEC_Distillation_TwoQubitOperations_Parity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:21:01.39496+00:00
-- url     : https://prove2.me/theorems/2c3216c2-50ca-4180-9af8-3e54077ce5f9
-- title:
--   Parity
-- statement:
--   Definitions and structural lemmas for Parity, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace TwoQubit
open Semantics Semantics.Qubit
def zzOperator : Operator TwoQubitSpace :=
  localZ 0 * localZ 1
def zzEvenProjector : Operator TwoQubitSpace :=
  (2 : Complex)⁻¹ • (1 + zzOperator)
def zzOddProjector : Operator TwoQubitSpace :=
  (2 : Complex)⁻¹ • (1 - zzOperator)
end TwoQubit
end Distillation
end QEC


