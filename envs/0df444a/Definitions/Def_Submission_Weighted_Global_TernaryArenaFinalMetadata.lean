-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalMetadata
-- name    : Submission_Weighted_Global_TernaryArenaFinalMetadata
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:54:58.070845+00:00
-- url     : https://prove2.me/theorems/f4ba3702-5125-4b84-bf46-8d1aa00c4bf7
-- title:
--   Ternary Arena Final Metadata
-- statement:
--   Definitions and structural lemmas for Ternary Arena Final Metadata, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedScoreReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostMemory
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFull
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaFinalMetadata
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory WeightedGlobalArenaPostMemory
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F r : ℕ} [Fact p.Prime]
end ThreeSum.WeightedGlobalArenaFinalMetadata


