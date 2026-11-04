-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryPairedBudgetCollision
-- name    : Submission_Weighted_Global_TernaryPairedBudgetCollision
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:40:27.609031+00:00
-- url     : https://prove2.me/theorems/df656579-c1cc-4e38-bf6a-a4d865444c1a
-- title:
--   Ternary Paired Budget Collision
-- statement:
--   Definitions and structural lemmas for Ternary Paired Budget Collision, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedBudgetCollision.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_ThreeSum_TernaryPairedBudgetSelector
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalPairedBudgetCollision
open Real WeightedGlobalPairedCollisionRate WeightedGlobalOversizePrime WeightedGlobalCoverScale WeightedGlobalLocalParameters
end ThreeSum.WeightedGlobalPairedBudgetCollision


