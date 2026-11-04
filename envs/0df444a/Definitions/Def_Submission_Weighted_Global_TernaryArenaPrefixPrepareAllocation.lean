-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
-- name    : Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:18:14.501632+00:00
-- url     : https://prove2.me/theorems/ad5b6cc8-9848-465f-a861-a299c017fa36
-- title:
--   Ternary Arena Prefix Prepare Allocation
-- statement:
--   Definitions and structural lemmas for Ternary Arena Prefix Prepare Allocation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPrepareAllocation.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepare
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
end ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation


