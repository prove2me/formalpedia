-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryNativePairAccess
-- name    : Submission_Weighted_Global_TernaryNativePairAccess
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:09:06.987086+00:00
-- url     : https://prove2.me/theorems/10d27ffe-f927-4d43-aa5d-2ef66c65479c
-- title:
--   Ternary Native Pair Access
-- statement:
--   Definitions and structural lemmas for Ternary Native Pair Access, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairAccess.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalNativeCompleteness
import Definitions.Def_Submission_Weighted_Global_TernaryCompactPairedSupport
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalNativePairAccess
open Finset TernaryJointType WeightedGlobalNativePairMoments TernarySourceHostModel
set_option maxHeartbeats 2000000
end ThreeSum.WeightedGlobalNativePairAccess


