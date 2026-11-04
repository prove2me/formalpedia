-- Prove2me | Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
-- name    : Submission_ThreeSum_LocalKeyArraySemantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:12:07.718271+00:00
-- url     : https://prove2.me/theorems/1d20f598-0f03-4731-8bfb-72f9e4a0134e
-- title:
--   Local Key Array Semantics
-- statement:
--   Definitions and structural lemmas for Local Key Array Semantics, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalKeyArraySemantics.lean

import Definitions.Def_Submission_ThreeSum_OutputKeyMasks
import Definitions.Def_Submission_ThreeSum_LightLocalKeys
set_option autoImplicit false
namespace ThreeSum.LocalKeyArraySemantics
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open Light
set_option maxHeartbeats 1800000
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LocalKeyArraySemantics


