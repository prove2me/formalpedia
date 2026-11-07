-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
-- name    : QEC_Coding_HypergraphProduct_Distance_Witness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:09:54.13603+00:00
-- url     : https://prove2.me/theorems/b08d73f2-3dc6-4345-b3b3-96337c6b1007
-- title:
--   Witness
-- statement:
--   Definitions and structural lemmas for Witness, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u v
def firstBlockWord
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Mul F] [Zero F]
    (x : Word F colOne) (y : Word F colTwo) :
    Word F (QubitIndex rowOne colOne rowTwo colTwo)
  | Sum.inl p => x p.1 * y p.2
  | Sum.inr _ => 0
def secondBlockWord
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Mul F] [Zero F]
    (x : Word F rowOne) (y : Word F rowTwo) :
    Word F (QubitIndex rowOne colOne rowTwo colTwo)
  | Sum.inl _ => 0
  | Sum.inr p => x p.1 * y p.2
end QEC.Coding.HypergraphProduct


