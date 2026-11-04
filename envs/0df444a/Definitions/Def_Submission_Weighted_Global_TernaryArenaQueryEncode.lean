-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryEncode
-- name    : Submission_Weighted_Global_TernaryArenaQueryEncode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:39:57.945277+00:00
-- url     : https://prove2.me/theorems/725357aa-831b-4543-9e22-cc92548126a4
-- title:
--   Ternary Arena Query Encode
-- statement:
--   Definitions and structural lemmas for Ternary Arena Query Encode, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryEncode.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryNative
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchInverse
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaQueryEncode
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaQueryModel WeightedGlobalGoodOutputCatalog
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]
end ThreeSum.WeightedGlobalArenaQueryEncode


