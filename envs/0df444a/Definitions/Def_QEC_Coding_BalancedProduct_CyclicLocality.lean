-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
-- name    : QEC_Coding_BalancedProduct_CyclicLocality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:58:24.755058+00:00
-- url     : https://prove2.me/theorems/3d883143-f242-46a9-b2eb-cf3fc7b10f82
-- title:
--   Cyclic Locality
-- statement:
--   Definitions and structural lemmas for Cyclic Locality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicLocality.lean

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BalancedProduct.CyclicLocality
open QEC.Coding
open PKDistance
universe u v
def dropUnitEquiv (I G : Type*) : I × Unit × G ≃ I × G where
  toFun p := (p.1, p.2.2)
  invFun p := (p.1, (), p.2)
  left_inv p := by rcases p with ⟨i, u, g⟩; cases u; rfl
  right_inv p := by rcases p with ⟨i, g⟩; rfl
end QEC.Coding.BalancedProduct.CyclicLocality


