-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
-- name    : Submission_Weighted_Global_TernaryArenaPrefixCommit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:48:47.420035+00:00
-- url     : https://prove2.me/theorems/8856adf0-753c-4c46-8a73-5f108025f966
-- title:
--   Ternary Arena Prefix Commit
-- statement:
--   Definitions and structural lemmas for Ternary Arena Prefix Commit, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixCommit.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixFinish
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPrefixCommit
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixFinish
end ThreeSum.WeightedGlobalArenaPrefixCommit


