-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPrepare
-- name    : Submission_ThreeSum_LightTernaryFrozenQueryPrepare
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:46:04.644117+00:00
-- url     : https://prove2.me/theorems/2cff0d85-c24f-4279-b9b7-da0c25b16b02
-- title:
--   Light Ternary Frozen Query Prepare
-- statement:
--   Definitions and structural lemmas for Light Ternary Frozen Query Prepare, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryPrepare.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryBranches
set_option autoImplicit false
namespace ThreeSum.LightTernaryFrozenQuery
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}
def prepTime (N : ℕ) : ℕ :=
  LightTernaryCodes.digitTime (2*N)+LightTernaryCodes.zeroTime (2*N)+LightMaskErase.time (2*N)+300
end ThreeSum.LightTernaryFrozenQuery


