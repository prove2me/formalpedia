-- Prove2me | Definitions.Def_QEC_Semantics_Channels_TraceNorm
-- name    : QEC_Semantics_Channels_TraceNorm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:47:02.026757+00:00
-- url     : https://prove2.me/theorems/56221765-4e3f-4a0f-86ed-3e7e2176a58d
-- title:
--   Trace Norm
-- statement:
--   Definitions and structural lemmas for Trace Norm, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/TraceNorm.lean

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
set_option autoImplicit false
universe u
namespace QEC.Semantics
open scoped ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QuantumChannel
variable {K L : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
end QuantumChannel
end
end QEC.Semantics


