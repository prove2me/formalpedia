-- Prove2me | Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
-- name    : QEC_Coding_CodeReduction_Classical_Distance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:52:57.625202+00:00
-- url     : https://prove2.me/theorems/60fc735d-f1b2-4f1e-afd3-404624dec1d1
-- title:
--   Distance
-- statement:
--   Definitions and structural lemmas for Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
set_option autoImplicit false
namespace QEC.Coding
open scoped BigOperators
universe u v w
namespace ClassicalWeightReduction
variable {F Check Bit : Type u} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
end ClassicalWeightReduction
end QEC.Coding


