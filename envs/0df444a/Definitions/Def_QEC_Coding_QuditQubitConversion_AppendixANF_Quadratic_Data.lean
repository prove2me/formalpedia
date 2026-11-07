-- Prove2me | Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
-- name    : QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:24:03.321778+00:00
-- url     : https://prove2.me/theorems/9887ccab-eece-403a-98ba-2f3a7011ad08
-- title:
--   Data
-- statement:
--   Definitions and structural lemmas for Data, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/Data.lean

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Certificate
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.Why24AppendixANF
def quadraticGatePairs : List (Fin 10 × Fin 10) :=
  [(0, 1), (0, 4), (0, 6), (0, 9),
   (1, 2), (1, 5), (1, 7),
   (2, 3), (2, 6), (2, 8),
   (3, 4), (3, 7), (3, 9),
   (4, 5), (4, 8),
   (5, 6), (5, 9),
   (6, 7), (7, 8), (8, 9)]
def quadraticGateCoefficient (left right : Fin 10) : ZMod 2 :=
  if (left, right) ∈ quadraticGatePairs then 1 else 0
def sourcePairCoefficient (left right : Fin 10) : ZMod 2 :=
  sourceCoefficient {left, right}
end QEC.Coding.Why24AppendixANF


