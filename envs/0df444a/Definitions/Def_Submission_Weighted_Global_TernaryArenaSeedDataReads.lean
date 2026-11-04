-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedDataReads
-- name    : Submission_Weighted_Global_TernaryArenaSeedDataReads
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T21:23:19.347174+00:00
-- url     : https://prove2.me/theorems/d2f83ae4-b426-460c-b653-47e463d75bd7
-- title:
--   Ternary Arena Seed Data Reads
-- statement:
--   Definitions and structural lemmas for Ternary Arena Seed Data Reads, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedDataReads.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedData
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSeedDataReads
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaLayout WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedData TernaryExtensionEncoding TernaryOriginalRowMenu
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 6000000
end ThreeSum.WeightedGlobalArenaSeedDataReads


