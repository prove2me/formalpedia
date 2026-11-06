-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
-- name    : QEC_Coding_BalancedProduct_LiftedProductDuality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:05:10.142175+00:00
-- url     : https://prove2.me/theorems/46cc96a9-aeee-444f-8e07-8e0af9be6155
-- title:
--   Lifted Product Duality
-- statement:
--   Definitions and structural lemmas for Lifted Product Duality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LiftedProductDuality.lean

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
set_option autoImplicit false
namespace QEC.Coding.BalancedProduct.LiftedProductDuality
open QEC.Coding
universe u v
def swapWord {F A B : Type*} (z : Word F (Sum A B)) : Word F (Sum B A)
  | Sum.inl b => z (Sum.inr b)
  | Sum.inr a => z (Sum.inl a)
def dualData
    {F G aRow aCol bRow bCol : Type*}
    [Semiring F] [Group G]
    (D : LiftedProduct.Data F G aRow aCol bRow bCol) :
    LiftedProduct.Data F G aCol aRow bCol bRow where
  A := LiftedProduct.starTranspose D.A
  B := LiftedProduct.starTranspose D.B
end QEC.Coding.BalancedProduct.LiftedProductDuality


