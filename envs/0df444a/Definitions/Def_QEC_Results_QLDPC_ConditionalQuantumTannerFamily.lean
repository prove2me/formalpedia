-- Prove2me | Definitions.Def_QEC_Results_QLDPC_ConditionalQuantumTannerFamily
-- name    : QEC_Results_QLDPC_ConditionalQuantumTannerFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T01:10:14.895227+00:00
-- url     : https://prove2.me/theorems/f16db987-2925-45b1-8f00-f203179eb1bb
-- title:
--   Conditional Quantum Tanner Family
-- statement:
--   Definitions and structural lemmas for Conditional Quantum Tanner Family, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/ConditionalQuantumTannerFamily.lean

import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGoodness
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.ArithmeticPSLFamily
open Classical QEC.Coding.ExpanderCodes.QuaternionGenerators QEC.Coding.SmallSetExpansion
attribute [local irreducible] fintypeTorusIndex cayleySquareFintype Family.ofData
end QEC.Coding.QuantumTanner.ArithmeticPSLFamily


