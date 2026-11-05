-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedDataReads
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedDataReads
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:55:37.430201+00:00
-- url     : https://prove2.me/theorems/2584f0df-cdf4-45de-af90-cbb982d1509c
-- title:
--   TernaryArenaSeedDataReads
-- statement:
--   Definitions and structural lemmas for TernaryArenaSeedDataReads, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSeedDataReads.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedData
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSeedDataReads
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaLayout WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedData TernaryExtensionEncoding TernaryOriginalRowMenu
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 6000000
end ThreeSum.WeightedGlobalArenaSeedDataReads
end
end WeightedCache3SUMRefinement_e1ae71d


