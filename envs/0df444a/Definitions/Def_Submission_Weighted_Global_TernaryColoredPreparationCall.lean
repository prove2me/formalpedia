-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredPreparationCall
-- name    : Submission_Weighted_Global_TernaryColoredPreparationCall
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:22:11.193325+00:00
-- url     : https://prove2.me/theorems/96a1c1e0-455f-47f5-9f23-cb2f1111a720
-- title:
--   Ternary Colored Preparation Call
-- statement:
--   Definitions and structural lemmas for Ternary Colored Preparation Call, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationCall.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredPreparationCall
open Light LightWeightedGlobalColoredSolver
set_option maxHeartbeats 2000000
set_option maxRecDepth 24000
end ThreeSum.WeightedGlobalColoredPreparationCall


