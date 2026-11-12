-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
-- name    : QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:29:57.5334+00:00
-- url     : https://prove2.me/theorems/3f1f0d87-01f1-4b2c-873c-97d46001aa51
-- title:
--   Parameter Sequence
-- statement:
--   Definitions and structural lemmas for Parameter Sequence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSequence.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
set_option autoImplicit false
namespace QEC.Distillation.HH18.HH18ParameterSequence
open Coding.PuncturedReedMuller
def p0 : ℚ := 270629 / 1000000
def p0R (j : Nat) : Nat := 1000000 * j
def p0W (j : Nat) : Nat := 811887 * j
def p0M (j : Nat) : Nat := 3 * p0R j + 1
end QEC.Distillation.HH18.HH18ParameterSequence


