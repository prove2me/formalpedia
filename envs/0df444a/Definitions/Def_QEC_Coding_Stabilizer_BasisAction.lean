-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_BasisAction
-- name    : QEC_Coding_Stabilizer_BasisAction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:23:42.918371+00:00
-- url     : https://prove2.me/theorems/ec8f1501-d96c-4b9a-8bc6-0e5f00e1460a
-- title:
--   Basis Action
-- statement:
--   Definitions and structural lemmas for Basis Action, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/BasisAction.lean

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.PauliSymplectic
open Semantics
universe u
variable {J : Type u} [Fintype J] [DecidableEq J]
end QEC.Coding.PauliSymplectic


