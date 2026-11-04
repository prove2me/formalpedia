-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
-- name    : Submission_Weighted_Global_TernaryPairedCollisionRate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:29:58.877907+00:00
-- url     : https://prove2.me/theorems/7aa8219c-2cab-4b3b-9354-99eca69022c9
-- title:
--   Ternary Paired Collision Rate
-- statement:
--   Definitions and structural lemmas for Ternary Paired Collision Rate, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedCollisionRate.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalPairedCollisionRate
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalCoverScale WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 1000000
def charge (K m : ℕ) : ℝ :=
  2-2*(nativeRate K m-Real.log 9/((fixedLength m : ℝ)*Real.log 2))/outputRate m
end ThreeSum.WeightedGlobalPairedCollisionRate


