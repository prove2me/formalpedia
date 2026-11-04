-- Prove2me | Definitions.Def_Submission_Weighted_FrozenPrepare
-- name    : Submission_Weighted_FrozenPrepare
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:46:01.032492+00:00
-- url     : https://prove2.me/theorems/ebfc949c-cb52-470f-8c7d-891ba4a9016c
-- title:
--   Frozen Prepare
-- statement:
--   Definitions and structural lemmas for Frozen Prepare, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenPrepare.lean

import Definitions.Def_Submission_Weighted_FrozenBranches
set_option autoImplicit false
namespace ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
def prepTime (N : ℕ) : ℕ :=
  LightTernaryCodes.digitTime (2*N)+LightTernaryCodes.zeroTime (2*N)+LightMaskErase.time (2*N)+300
end ThreeSum.LightWeightedFrozenQuery


