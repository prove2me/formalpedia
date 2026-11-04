-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryCompactPairedSupport
-- name    : Submission_Weighted_Global_TernaryCompactPairedSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:59:04.171469+00:00
-- url     : https://prove2.me/theorems/7343f39b-663e-4647-80a7-7660b29c210a
-- title:
--   Ternary Compact Paired Support
-- statement:
--   Definitions and structural lemmas for Ternary Compact Paired Support, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCompactPairedSupport.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Definitions.Def_Submission_Weighted_Global_TernaryPairedSelectedChain
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalCompactPairedSupport
open LightOriginalSurvivors LightOriginalCollisionCleanup LightOriginalBucketFilter
open TernaryPairedSupportConcrete TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable
end ThreeSum.WeightedGlobalCompactPairedSupport


