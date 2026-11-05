-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCollisionRate
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCollisionRate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:25:58.647139+00:00
-- url     : https://prove2.me/theorems/fce5a2fb-06bc-4f0d-b52d-eac6c046611d
-- title:
--   TernaryPairedCollisionRate
-- statement:
--   Definitions and structural lemmas for TernaryPairedCollisionRate, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedCollisionRate.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalPairedCollisionRate
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalCoverScale WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 1000000
def charge (K m : ℕ) : ℝ :=
  2-2*(nativeRate K m-Real.log 9/((fixedLength m : ℝ)*Real.log 2))/outputRate m
end ThreeSum.WeightedGlobalPairedCollisionRate
end
end WeightedCache3SUMRefinement_e1ae71d


