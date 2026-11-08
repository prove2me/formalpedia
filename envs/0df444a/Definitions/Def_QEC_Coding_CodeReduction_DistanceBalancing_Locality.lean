-- Prove2me | Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
-- name    : QEC_Coding_CodeReduction_DistanceBalancing_Locality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:18:18.195202+00:00
-- url     : https://prove2.me/theorems/d6cae8c0-042f-43fb-8b63-71867251c9e7
-- title:
--   Locality
-- statement:
--   Definitions and structural lemmas for Locality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
set_option autoImplicit false
namespace QEC.Coding.DistanceBalancing
universe u
open QEC.Coding.FiberBundle
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
end QEC.Coding.DistanceBalancing


