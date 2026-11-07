-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
-- name    : QEC_Coding_HypergraphProduct_Diagonal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:15:28.679949+00:00
-- url     : https://prove2.me/theorems/adbad038-453c-475f-a938-6f1183eb609d
-- title:
--   Diagonal
-- statement:
--   Definitions and structural lemmas for Diagonal, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u v
def diagonalData
    {F : Type v} {Row Col : Type u} (H : Matrix Row Col F) :
    Data F Row Col Row Col where
  first := H
  second := H
end QEC.Coding.HypergraphProduct


