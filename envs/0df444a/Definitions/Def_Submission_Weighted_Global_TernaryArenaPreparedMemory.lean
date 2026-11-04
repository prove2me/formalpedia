-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaPreparedMemory
-- name    : Submission_Weighted_Global_TernaryArenaPreparedMemory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:38:28.349217+00:00
-- url     : https://prove2.me/theorems/e2f3dd09-934c-4990-ac3c-83846b910300
-- title:
--   Ternary Arena Prepared Memory
-- statement:
--   Definitions and structural lemmas for Ternary Arena Prepared Memory, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPreparedMemory.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixState
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepare
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixPreparedHeader
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPreparedMemory
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
end ThreeSum.WeightedGlobalArenaPreparedMemory


