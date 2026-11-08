-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
-- name    : QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:12:19.314215+00:00
-- url     : https://prove2.me/theorems/a68cdd0f-9b83-4c51-aeeb-4c2c600de3f5
-- title:
--   XLocal Weight Parity
-- statement:
--   Definitions and structural lemmas for XLocal Weight Parity, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightParity.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace QEC.Coding.BDL26XLocalWeightParity
open scoped BigOperators
def bitWeight (b : ZMod 2) : ℕ := if b = 0 then 0 else 1
def pieceCrossingCost (a b l r : ZMod 2) : ℕ :=
  bitWeight a + bitWeight b + bitWeight l + bitWeight r - bitWeight (a + b)
def pieceCrossingCoefficients (a b l r : ZMod 2) (i : Fin 5) : ZMod 2 :=
  if a + b = 0 then
    if i = 0 then a else if i = 2 then b else if i = 4 then r else 0
  else
    if i = 0 then a * l else if i = 1 then a * r else
      if i = 2 then b * l else if i = 3 then b * r else 0
end QEC.Coding.BDL26XLocalWeightParity


