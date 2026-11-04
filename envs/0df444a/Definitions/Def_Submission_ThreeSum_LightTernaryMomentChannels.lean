-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels
-- name    : Submission_ThreeSum_LightTernaryMomentChannels
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:43:49.942803+00:00
-- url     : https://prove2.me/theorems/02d36211-a16c-4765-ba0b-1c36782139b9
-- title:
--   Light Ternary Moment Channels
-- statement:
--   Definitions and structural lemmas for Light Ternary Moment Channels, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannels.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
set_option autoImplicit false
namespace ThreeSum.LightTernaryMomentChannels
open Light LightFixedArithmetic TernaryWeightChannels
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightTernaryMomentChannels


