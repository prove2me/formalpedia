-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
-- name    : QEC_Coding_FiberBundle_WeightReductionParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:16:53.367789+00:00
-- url     : https://prove2.me/theorems/9e984b65-46b2-473f-bd6e-48444b905ff8
-- title:
--   Weight Reduction Parameters
-- statement:
--   Definitions and structural lemmas for Weight Reduction Parameters, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
namespace QEC.Coding.FiberBundle
open scoped BigOperators
universe u v
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
namespace RandomBase
end RandomBase
end QEC.Coding.FiberBundle


