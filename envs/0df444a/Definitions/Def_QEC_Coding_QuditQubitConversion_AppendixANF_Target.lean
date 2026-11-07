-- Prove2me | Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
-- name    : QEC_Coding_QuditQubitConversion_AppendixANF_Target
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:42:24.54997+00:00
-- url     : https://prove2.me/theorems/6f03863a-4f3f-4c07-8ce2-5e395ceccb87
-- title:
--   Target
-- statement:
--   Definitions and structural lemmas for Target, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Target.lean

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Symbolic
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
def gateCoefficient (support : Finset (Fin 10)) : ZMod 2 :=
  if hsingle : support.card = 1 then 1
  else if hpair : support.card = 2 then
    quadraticGateCoefficient
      (support.orderEmbOfFin hpair (0 : Fin 2))
      (support.orderEmbOfFin hpair (1 : Fin 2))
  else if htriple : support.card = 3 then
    cubicGateCoefficient
      (support.orderEmbOfFin htriple (0 : Fin 3))
      (support.orderEmbOfFin htriple (1 : Fin 3))
      (support.orderEmbOfFin htriple (2 : Fin 3))
  else 0
def expandedGateCoefficient (support : Finset (Fin 10)) : ZMod 2 :=
  (∑ coordinate : Fin 10, if {coordinate} = support then 1 else 0) +
  (∑ left : Fin 10, ∑ right : Fin 10,
    if left < right ∧ {left, right} = support then
      quadraticGateCoefficient left right
    else 0) +
  (∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
    if first < second ∧ second < third ∧
        {first, second, third} = support then
      cubicGateCoefficient first second third
    else 0)
def gatePhasePolynomial : ANF :=
  (∑ coordinate : Fin 10, generator coordinate) +
  (∑ left : Fin 10, ∑ right : Fin 10,
    if left < right then
      quadraticGateCoefficient left right • (generator left * generator right)
    else 0) +
  (∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
    if first < second ∧ second < third then
      cubicGateCoefficient first second third •
        (generator first * generator second * generator third)
    else 0)
end QEC.Coding.Why24AppendixANF


