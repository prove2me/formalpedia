-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Realization
-- name    : QEC_Coding_HypergraphProduct_Dimension_Realization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:30:20.885257+00:00
-- url     : https://prove2.me/theorems/ee9c92ed-8df2-4c48-948b-b5859244523a
-- title:
--   Realization
-- statement:
--   Definitions and structural lemmas for Realization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Realization.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Coordinates
import Definitions.Def_QEC_Coding_ChainComplex_Duality
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u v w
open TensorProduct
def wordTensorEquiv
    (F : Type u) (A : Type v) (B : Type w)
    [Field F] [Fintype B] [DecidableEq B] :
    (Word F A ⊗[F] Word F B) ≃ₗ[F] Word F (A × B) :=
  (TensorProduct.piScalarRight F F (Word F A) B).trans
    ((LinearEquiv.curry F F B A).symm.trans
      (LinearEquiv.funCongrLeft F F (Equiv.prodComm A B)))
def wordSumEquiv (F : Type u) (A : Type v) (B : Type w) [Semiring F] :
    Word F (Sum A B) ≃ₗ[F] Word F A × Word F B :=
  LinearEquiv.sumPiEquivProdPi F A B (fun _ => F)
def wordSumEquivSwap (F : Type u) (A : Type v) (B : Type w) [Semiring F] :
    Word F (Sum A B) ≃ₗ[F] Word F B × Word F A :=
  (wordSumEquiv F A B).trans (LinearEquiv.prodComm F (Word F A) (Word F B))
end QEC.Coding.HypergraphProduct


