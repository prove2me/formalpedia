-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTensorBridge
-- name    : QEC_Coding_QuantumTanner_LiftedProductTensorBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:22:55.420836+00:00
-- url     : https://prove2.me/theorems/0d0e12b7-008c-4958-934c-3cf2a6b1ad75
-- title:
--   Lifted Product Tensor Bridge
-- statement:
--   Definitions and structural lemmas for Lifted Product Tensor Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTensorBridge.lean

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductActionBridge
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.LiftedProductTensorBridge
open Classical
universe v
variable {A B C D : Type v} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
def matrixRowCode (P : Matrix C A (ZMod 2)) : LinearCode (ZMod 2) A :=
  parityCheckRowCode (Matrix.toLin' P)
def tensorMatrix (P : Matrix C A (ZMod 2)) (Q : Matrix D B (ZMod 2))
    (U : Matrix C D (ZMod 2)) : Word (ZMod 2) (A × B) :=
  fun ij => ∑ c, ∑ d, U c d * P c ij.1 * Q d ij.2
end QEC.Coding.QuantumTanner.LiftedProductTensorBridge


