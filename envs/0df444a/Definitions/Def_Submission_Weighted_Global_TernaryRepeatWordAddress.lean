-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryRepeatWordAddress
-- name    : Submission_Weighted_Global_TernaryRepeatWordAddress
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:12:07.039558+00:00
-- url     : https://prove2.me/theorems/797ab3e6-12af-4853-abd2-47f46be3e0fe
-- title:
--   Ternary Repeat Word Address
-- statement:
--   Definitions and structural lemmas for Ternary Repeat Word Address, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatWordAddress.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryRepeatWord
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalRepeatWordAddress
open ThreeSum.LightTernaryRepeatWord
open TernaryJointType
set_option maxHeartbeats 2000000
end ThreeSum.WeightedGlobalRepeatWordAddress


