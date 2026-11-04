-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredSeedABI
-- name    : Submission_Weighted_Global_TernaryColoredSeedABI
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:21:17.508581+00:00
-- url     : https://prove2.me/theorems/67e1293e-c5a8-407c-94bc-09bc9d8cb02a
-- title:
--   Ternary Colored Seed ABI
-- statement:
--   Definitions and structural lemmas for Ternary Colored Seed ABI, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSeedABI.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredInitializationProof
import Definitions.Def_Submission_Weighted_Global_TernaryArenaInitialSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredSeedABI
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixFinish
open LightWeightedGlobalColoredInitializationProof
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
end ThreeSum.WeightedGlobalColoredSeedABI


