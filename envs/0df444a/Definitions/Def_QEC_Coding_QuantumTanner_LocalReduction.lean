-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_LocalReduction
-- name    : QEC_Coding_QuantumTanner_LocalReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:29:01.542986+00:00
-- url     : https://prove2.me/theorems/69734038-d282-433d-9d8c-c8500e3a2543
-- title:
--   Local Reduction
-- statement:
--   Definitions and structural lemmas for Local Reduction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LocalReduction.lean

import Definitions.Def_QEC_Coding_QuantumTanner_TensorApproximation
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]
end QEC.Coding.QuantumTanner


