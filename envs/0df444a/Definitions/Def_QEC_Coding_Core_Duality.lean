-- Prove2me | Definitions.Def_QEC_Coding_Core_Duality
-- name    : QEC_Coding_Core_Duality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:09:45.357956+00:00
-- url     : https://prove2.me/theorems/ae7a4ea8-cfc9-47e2-b8ed-a4ed591c1d22
-- title:
--   Duality
-- statement:
--   Definitions and structural lemmas for Duality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Duality.lean

import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.LinearCode
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
end QEC.Coding.LinearCode


