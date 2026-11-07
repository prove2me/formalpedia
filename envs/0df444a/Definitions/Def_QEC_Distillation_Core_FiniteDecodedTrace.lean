-- Prove2me | Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
-- name    : QEC_Distillation_Core_FiniteDecodedTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:11:37.920372+00:00
-- url     : https://prove2.me/theorems/e3399b1a-0128-4601-b3fa-7cf1cafec9d7
-- title:
--   Finite Decoded Trace
-- statement:
--   Definitions and structural lemmas for Finite Decoded Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteDecodedTrace.lean

import Definitions.Def_QEC_Distillation_Core_FiniteCentering
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace FiniteDecodedTrace
open Semantics
open scoped BigOperators
universe u v
end FiniteDecodedTrace
end Distillation
end QEC


