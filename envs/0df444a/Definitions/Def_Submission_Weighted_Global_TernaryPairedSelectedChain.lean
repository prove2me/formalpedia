-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryPairedSelectedChain
-- name    : Submission_Weighted_Global_TernaryPairedSelectedChain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:41:31.205137+00:00
-- url     : https://prove2.me/theorems/957d4a5c-0a6d-4e65-ae3d-0ab0fc24f5bb
-- title:
--   Ternary Paired Selected Chain
-- statement:
--   Definitions and structural lemmas for Ternary Paired Selected Chain, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedSelectedChain.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalPairedSelectedChain
open Filter Real Finset TernaryPairedRecurrence TernaryPairedInitial WeightedGlobalPairedNativeDrift
open WeightedGlobalOversizePrime WeightedGlobalOversizeOverhead WeightedGlobalCoverScale WeightedGlobalLocalParameters TernaryCoverLocal
open WeightedGlobalEntropyRates
open WeightedGlobalSignedPadding TernaryPairedPotential TernaryPairedSupportConcrete
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
end ThreeSum.WeightedGlobalPairedSelectedChain


