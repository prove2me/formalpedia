-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
-- name    : QEC_Coding_QuantumTanner_ViewAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:26:49.788163+00:00
-- url     : https://prove2.me/theorems/0309ad13-544e-4863-924f-017b1d2f3cbe
-- title:
--   View Assembly
-- statement:
--   Definitions and structural lemmas for View Assembly, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ViewAssembly.lean

import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]
end QEC.Coding.QuantumTanner


