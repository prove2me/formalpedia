-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalGuardAllocation
-- name    : Submission_Weighted_Global_TernaryArenaFinalGuardAllocation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:16:37.025221+00:00
-- url     : https://prove2.me/theorems/29e198a8-e347-45ff-a5c3-bda14991a53a
-- title:
--   Ternary Arena Final Guard Allocation
-- statement:
--   Definitions and structural lemmas for Ternary Arena Final Guard Allocation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalGuardAllocation.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceArithmetic
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaFinalGuardAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalArenaAllocation
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
variable {p m F r : ℕ} [Fact p.Prime]
end ThreeSum.WeightedGlobalArenaFinalGuardAllocation


