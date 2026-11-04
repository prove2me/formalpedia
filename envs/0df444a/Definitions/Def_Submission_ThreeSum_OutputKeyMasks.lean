-- Prove2me | Definitions.Def_Submission_ThreeSum_OutputKeyMasks
-- name    : Submission_ThreeSum_OutputKeyMasks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:08:47.16248+00:00
-- url     : https://prove2.me/theorems/b855a6ef-763a-43f9-b739-dc4e5d7e7591
-- title:
--   Output Key Masks
-- statement:
--   Definitions and structural lemmas for Output Key Masks, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputKeyMasks.lean

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
set_option autoImplicit false
namespace ThreeSum.OutputKeyMasks
open GlobalEncoding LocalHashMoments LocalCoverBounds
open OneHotMask SubsetAddress
open scoped BigOperators
end ThreeSum.OutputKeyMasks


