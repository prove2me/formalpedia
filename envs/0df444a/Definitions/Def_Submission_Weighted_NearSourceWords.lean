-- Prove2me | Definitions.Def_Submission_Weighted_NearSourceWords
-- name    : Submission_Weighted_NearSourceWords
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:01:00.852223+00:00
-- url     : https://prove2.me/theorems/9ab0370d-a6fc-4ace-954f-5083d4319027
-- title:
--   Near Source Words
-- statement:
--   Definitions and structural lemmas for Near Source Words, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearSourceWords.lean

import Definitions.Def_Submission_Weighted_NearSource
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedNearSourceWords
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.WeightedPhysicalEuler
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
end ThreeSum.LightWeightedNearSourceWords


