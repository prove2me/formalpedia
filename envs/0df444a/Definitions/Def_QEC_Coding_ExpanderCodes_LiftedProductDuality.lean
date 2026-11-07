-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
-- name    : QEC_Coding_ExpanderCodes_LiftedProductDuality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:24:33.562942+00:00
-- url     : https://prove2.me/theorems/3985dd47-f4e3-4ea3-b6a7-0af616e83aee
-- title:
--   Lifted Product Duality
-- statement:
--   Definitions and structural lemmas for Lifted Product Duality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
set_option autoImplicit false
namespace QEC.Coding.LiftedProduct
universe u v
def signedSwapWord {F A B : Type*} [Neg F]
    (z : Word F (Sum A B)) : Word F (Sum B A)
  | Sum.inl b => z (Sum.inr b)
  | Sum.inr a => -z (Sum.inl a)
def signedUnswapWord {F A B : Type*} [Neg F]
    (z : Word F (Sum B A)) : Word F (Sum A B) :=
  -signedSwapWord z
def dualData
    {F G aRow aCol bRow bCol : Type*}
    [Semiring F] [Group G]
    (D : Data F G aRow aCol bRow bCol) :
    Data F G aCol aRow bCol bRow where
  A := starTranspose D.A
  B := starTranspose D.B
end QEC.Coding.LiftedProduct


