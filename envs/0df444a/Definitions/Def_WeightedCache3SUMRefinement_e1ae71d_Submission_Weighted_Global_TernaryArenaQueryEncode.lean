-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryEncode
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryEncode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:25:24.378957+00:00
-- url     : https://prove2.me/theorems/3ef03ed9-f3a9-4ac7-ad0b-5099ff8ba6a3
-- title:
--   TernaryArenaQueryEncode
-- statement:
--   Definitions and structural lemmas for TernaryArenaQueryEncode, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaQueryEncode.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryNative
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchInverse
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaQueryEncode
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaQueryModel WeightedGlobalGoodOutputCatalog
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]
end ThreeSum.WeightedGlobalArenaQueryEncode
end
end WeightedCache3SUMRefinement_e1ae71d


