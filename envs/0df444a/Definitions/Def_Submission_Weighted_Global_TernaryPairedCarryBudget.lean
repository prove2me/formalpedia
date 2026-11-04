-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryPairedCarryBudget
-- name    : Submission_Weighted_Global_TernaryPairedCarryBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:22:57.551207+00:00
-- url     : https://prove2.me/theorems/0ba66327-a46c-4eab-8096-3c6ad713f2c2
-- title:
--   Ternary Paired Carry Budget
-- statement:
--   Definitions and structural lemmas for Ternary Paired Carry Budget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedCarryBudget.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalPairedCarryBudget
open Filter Real WeightedGlobalSignedPreparationBudget WeightedGlobalSignedPadding WeightedGlobalCoverScale
open scoped Topology
end ThreeSum.WeightedGlobalPairedCarryBudget


