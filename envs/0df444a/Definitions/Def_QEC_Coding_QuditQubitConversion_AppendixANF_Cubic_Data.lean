-- Prove2me | Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
-- name    : QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:31:10.191263+00:00
-- url     : https://prove2.me/theorems/e28689c1-120e-4ba8-a644-1f7adef48b69
-- title:
--   Data
-- statement:
--   Definitions and structural lemmas for Data, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Data.lean

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Certificate
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.Why24AppendixANF
def cubicGateTriples : List (Fin 10 × Fin 10 × Fin 10) :=
  [(0, 1, 2), (0, 1, 4), (0, 1, 5), (0, 1, 7), (0, 1, 8),
   (0, 1, 9), (0, 2, 3), (0, 2, 4), (0, 2, 7), (0, 2, 8),
   (0, 3, 4), (0, 3, 5), (0, 3, 9), (0, 4, 9), (0, 5, 6),
   (0, 5, 8), (0, 6, 7), (0, 6, 8), (0, 6, 9), (0, 7, 9),
   (0, 8, 9),
   (1, 2, 3), (1, 2, 5), (1, 2, 6), (1, 2, 8), (1, 2, 9),
   (1, 3, 4), (1, 3, 5), (1, 3, 8), (1, 3, 9), (1, 4, 5),
   (1, 4, 6), (1, 6, 7), (1, 6, 9), (1, 7, 8), (1, 7, 9),
   (2, 3, 4), (2, 3, 6), (2, 3, 7), (2, 3, 9), (2, 4, 5),
   (2, 4, 6), (2, 4, 9), (2, 5, 6), (2, 5, 7), (2, 7, 8),
   (2, 8, 9),
   (3, 4, 5), (3, 4, 7), (3, 4, 8), (3, 5, 6), (3, 5, 7),
   (3, 6, 7), (3, 6, 8), (3, 8, 9),
   (4, 5, 6), (4, 5, 8), (4, 5, 9), (4, 6, 7), (4, 6, 8),
   (4, 7, 8), (4, 7, 9),
   (5, 6, 7), (5, 6, 9), (5, 7, 8), (5, 7, 9), (5, 8, 9),
   (6, 7, 8), (6, 8, 9), (7, 8, 9)]
def cubicGateCoefficient (first second third : Fin 10) : ZMod 2 :=
  if (first, second, third) ∈ cubicGateTriples then 1 else 0
def sourceTripleCoefficient (first second third : Fin 10) : ZMod 2 :=
  sourceCoefficient {first, second, third}
end QEC.Coding.Why24AppendixANF


