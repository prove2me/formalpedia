-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaPostResources
-- name    : Submission_Weighted_Global_TernaryArenaPostResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T17:46:18.428766+00:00
-- url     : https://prove2.me/theorems/d84b5704-94b7-49ed-97fd-1f366ef0d0e0
-- title:
--   Ternary Arena Post Resources
-- statement:
--   Definitions and structural lemmas for Ternary Arena Post Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostResources.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostMemory
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPostResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps LightWeightedGlobalPostSelection
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]
end ThreeSum.WeightedGlobalArenaPostResources


