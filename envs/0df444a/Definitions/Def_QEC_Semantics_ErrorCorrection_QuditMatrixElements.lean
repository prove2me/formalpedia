-- Prove2me | Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
-- name    : QEC_Semantics_ErrorCorrection_QuditMatrixElements
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:12:15.680092+00:00
-- url     : https://prove2.me/theorems/e17e6415-b02f-44fc-aca1-6241da505848
-- title:
--   Qudit Matrix Elements
-- statement:
--   Definitions and structural lemmas for Qudit Matrix Elements, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditMatrixElements.lean

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
set_option autoImplicit false
noncomputable section
namespace QEC.Semantics.QuditSubsystem
open scoped BigOperators TensorProduct
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] {q : J → Nat}
end QEC.Semantics.QuditSubsystem


