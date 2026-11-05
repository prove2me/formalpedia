-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryTime
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryTime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:20:07.391038+00:00
-- url     : https://prove2.me/theorems/f1906179-e7ac-44fe-9406-72b0d718c5b7
-- title:
--   TernaryArenaQueryTime
-- statement:
--   Definitions and structural lemmas for TernaryArenaQueryTime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaQueryTime.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCountReady
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaQueryTime
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup LightWeightedNearPair WeightedGlobalCountFrontendBudget
set_option maxHeartbeats 5000000
variable {p m F r : ℕ} [Fact p.Prime]
attribute [local instance] Classical.propDecidable
end ThreeSum.WeightedGlobalArenaQueryTime
end
end WeightedCache3SUMRefinement_e1ae71d


