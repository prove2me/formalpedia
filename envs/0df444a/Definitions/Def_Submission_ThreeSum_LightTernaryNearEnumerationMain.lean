-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumerationMain
-- name    : Submission_ThreeSum_LightTernaryNearEnumerationMain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:36:13.433952+00:00
-- url     : https://prove2.me/theorems/1379cf88-3f2a-4441-83f3-95e0426b9b11
-- title:
--   Light Ternary Near Enumeration Main
-- statement:
--   Definitions and structural lemmas for Light Ternary Near Enumeration Main, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumerationMain.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
set_option autoImplicit false
namespace ThreeSum.LightTernaryNearEnumerationMain
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration ThreeSum.LightTernaryNearEnumeration
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}
end ThreeSum.LightTernaryNearEnumerationMain


