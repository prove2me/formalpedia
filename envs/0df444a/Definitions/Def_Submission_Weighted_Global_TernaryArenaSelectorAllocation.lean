-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
-- name    : Submission_Weighted_Global_TernaryArenaSelectorAllocation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:17:32.722716+00:00
-- url     : https://prove2.me/theorems/81971040-fbff-491c-a717-26fa0143b815
-- title:
--   Ternary Arena Selector Allocation
-- statement:
--   Definitions and structural lemmas for Ternary Arena Selector Allocation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectorAllocation.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSelectorAllocation
open Light WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
end ThreeSum.WeightedGlobalArenaSelectorAllocation


