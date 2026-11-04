-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryNearSourceWords
-- name    : Submission_ThreeSum_LightTernaryNearSourceWords
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:00:57.971887+00:00
-- url     : https://prove2.me/theorems/326bed84-df7d-44ef-90b7-8e515b900d0a
-- title:
--   Light Ternary Near Source Words
-- statement:
--   Definitions and structural lemmas for Light Ternary Near Source Words, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearSourceWords.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryNearSource
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightTernaryNearSourceWords
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryPhysicalEuler
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
end ThreeSum.LightTernaryNearSourceWords


