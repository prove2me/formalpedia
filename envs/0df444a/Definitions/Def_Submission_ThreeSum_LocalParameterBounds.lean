-- Prove2me | Definitions.Def_Submission_ThreeSum_LocalParameterBounds
-- name    : Submission_ThreeSum_LocalParameterBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:43:07.5571+00:00
-- url     : https://prove2.me/theorems/2c74312e-3135-4022-adb1-3faee6bfe752
-- title:
--   Local Parameter Bounds
-- statement:
--   Definitions and structural lemmas for Local Parameter Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalParameterBounds.lean

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
set_option autoImplicit false
namespace ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000
def base (h : ℕ) : ℕ := 2^(2048*(h+1))
def envelope (h : ℕ) : ℕ := 2^(2048*(h+1)+2)
end ThreeSum.LocalParameterBounds


