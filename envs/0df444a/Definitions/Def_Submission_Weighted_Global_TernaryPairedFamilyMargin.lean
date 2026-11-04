-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryPairedFamilyMargin
-- name    : Submission_Weighted_Global_TernaryPairedFamilyMargin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:15:29.029906+00:00
-- url     : https://prove2.me/theorems/b07af073-88c3-4162-8988-e6403700ba6f
-- title:
--   Ternary Paired Family Margin
-- statement:
--   Definitions and structural lemmas for Ternary Paired Family Margin, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedFamilyMargin.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalPairedFamilyMargin
open Filter Real WeightedGlobalOversizeOverhead WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalParameters
open scoped Topology
set_option maxHeartbeats 1000000
def baseRate (m : ℕ) : ℝ :=
  (Real.log 9+361*Real.log 2+7*Real.log (m+1 : ℝ))/((fixedLength m : ℝ)*Real.log 2)
end ThreeSum.WeightedGlobalPairedFamilyMargin


