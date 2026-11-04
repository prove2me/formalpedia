-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI
-- name    : Submission_Weighted_Global_TernaryColoredPostABI
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T18:04:52.672641+00:00
-- url     : https://prove2.me/theorems/1c66e3f1-3e58-447a-824d-57247d0ae1d5
-- title:
--   Ternary Colored Post ABI
-- statement:
--   Definitions and structural lemmas for Ternary Colored Post ABI, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000
end ThreeSum.WeightedGlobalColoredPostABI


