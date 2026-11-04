-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryMain
-- name    : Submission_ThreeSum_LightTernaryFrozenQueryMain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:52:35.823206+00:00
-- url     : https://prove2.me/theorems/24a658ae-af09-4eae-9763-ace77c8fef77
-- title:
--   Light Ternary Frozen Query Main
-- statement:
--   Definitions and structural lemmas for Light Ternary Frozen Query Main, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryMain.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryTime
set_option autoImplicit false
namespace ThreeSum.LightTernaryFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
end ThreeSum.LightTernaryFrozenQuery


