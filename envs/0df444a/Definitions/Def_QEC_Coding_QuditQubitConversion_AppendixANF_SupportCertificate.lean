-- Prove2me | Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
-- name    : QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:45:24.70658+00:00
-- url     : https://prove2.me/theorems/b8498545-2f21-40ea-a00b-db932615e9d5
-- title:
--   Support Certificate
-- statement:
--   Definitions and structural lemmas for Support Certificate, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/SupportCertificate.lean

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.Why24AppendixANF
open scoped BigOperators
def linearContribution (support : Finset (Fin 10)) : ZMod 2 :=
  ∑ coordinate : Fin 10, if {coordinate} = support then 1 else 0
def pairContribution (support : Finset (Fin 10)) : ZMod 2 :=
  ∑ left : Fin 10, ∑ right : Fin 10,
    if left < right ∧ {left, right} = support then
      quadraticGateCoefficient left right
    else 0
def tripleContribution (support : Finset (Fin 10)) : ZMod 2 :=
  ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
    if first < second ∧ second < third ∧
        {first, second, third} = support then
      cubicGateCoefficient first second third
    else 0
end QEC.Coding.Why24AppendixANF


