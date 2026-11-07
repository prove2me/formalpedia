-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
-- name    : QEC_Coding_QuantumTanner_TensorPuncture
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:21:53.796383+00:00
-- url     : https://prove2.me/theorems/9fec9935-a576-4d8c-b547-29a653b18aa1
-- title:
--   Tensor Puncture
-- statement:
--   Definitions and structural lemmas for Tensor Puncture, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
def tensorPunctureMap (removedA : Finset A) (removedB : Finset B) :
    Word F (A × B) →ₗ[F] Word F (KeptCoordinate removedA × KeptCoordinate removedB) where
  toFun x ab := x (ab.1.1, ab.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end QEC.Coding.QuantumTanner


