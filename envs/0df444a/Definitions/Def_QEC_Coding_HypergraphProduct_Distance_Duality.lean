-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
-- name    : QEC_Coding_HypergraphProduct_Distance_Duality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:31:06.298981+00:00
-- url     : https://prove2.me/theorems/101dfc08-760b-4a19-a7bc-2873ca97284c
-- title:
--   Duality
-- statement:
--   Definitions and structural lemmas for Duality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u v
def swapWord {F A B : Type*} (x : Word F (Sum A B)) : Word F (Sum B A)
  | Sum.inl b => x (Sum.inr b)
  | Sum.inr a => x (Sum.inl a)
def transposeData
    {F rowOne colOne rowTwo colTwo : Type*}
    (D : Data F rowOne colOne rowTwo colTwo) :
    Data F colOne rowOne colTwo rowTwo where
  first := D.first.transpose
  second := D.second.transpose
end QEC.Coding.HypergraphProduct


