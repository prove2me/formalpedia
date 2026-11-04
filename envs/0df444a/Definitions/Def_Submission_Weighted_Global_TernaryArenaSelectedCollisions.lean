-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
-- name    : Submission_Weighted_Global_TernaryArenaSelectedCollisions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:06:30.277703+00:00
-- url     : https://prove2.me/theorems/a558e055-55b8-47ac-bf19-54815c304061
-- title:
--   Ternary Arena Selected Collisions
-- statement:
--   Definitions and structural lemmas for Ternary Arena Selected Collisions, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedCollisions.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSelectedCollisions
open WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalPairedCollisionRate
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedSigned WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 3000000
end ThreeSum.WeightedGlobalArenaSelectedCollisions


