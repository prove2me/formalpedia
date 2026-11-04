-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryNativePairedLineage
-- name    : Submission_Weighted_Global_TernaryNativePairedLineage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:54:25.43774+00:00
-- url     : https://prove2.me/theorems/72f0b7b0-870c-4588-8f46-74f3176a8c4e
-- title:
--   Ternary Native Paired Lineage
-- statement:
--   Definitions and structural lemmas for Ternary Native Paired Lineage, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairedLineage.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryPairedContraction
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalNativePairedLineage
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
set_option maxHeartbeats 3000000
end ThreeSum.WeightedGlobalNativePairedLineage


