-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedFamilyMargin
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedFamilyMargin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:21:02.422223+00:00
-- url     : https://prove2.me/theorems/34c5ce1e-447e-4516-a78a-2c0140031c57
-- title:
--   TernaryPairedFamilyMargin
-- statement:
--   Definitions and structural lemmas for TernaryPairedFamilyMargin, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedFamilyMargin.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalPairedFamilyMargin
open Filter Real WeightedGlobalOversizeOverhead WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalParameters
open scoped Topology
set_option maxHeartbeats 1000000
def baseRate (m : ℕ) : ℝ :=
  (Real.log 9+431*Real.log 2+7*Real.log (m+1 : ℝ))/((fixedLength m : ℝ)*Real.log 2)
end ThreeSum.WeightedGlobalPairedFamilyMargin
end
end WeightedCache3SUMRefinement_e1ae71d


