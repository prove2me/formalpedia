-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixCall
-- name    : Submission_Weighted_Global_TernaryColoredPrefixCall
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:08:48.78821+00:00
-- url     : https://prove2.me/theorems/6ec20ad7-4935-464c-b564-2c73f2ac89e1
-- title:
--   Ternary Colored Prefix Call
-- statement:
--   Definitions and structural lemmas for Ternary Colored Prefix Call, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPrefixCall.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredPrefixCall
open Light LightWeightedGlobalColoredSolver
set_option maxHeartbeats 1500000
set_option maxRecDepth 24000
end ThreeSum.WeightedGlobalColoredPrefixCall


