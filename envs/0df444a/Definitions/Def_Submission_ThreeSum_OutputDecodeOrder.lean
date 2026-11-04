-- Prove2me | Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
-- name    : Submission_ThreeSum_OutputDecodeOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:08:45.698582+00:00
-- url     : https://prove2.me/theorems/c9f3d386-0f3c-4a9c-9ad8-1f32a4261e67
-- title:
--   Output Decode Order
-- statement:
--   Definitions and structural lemmas for Output Decode Order, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOrder.lean

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSumApsp_Util_List
set_option autoImplicit false
namespace ThreeSum.OutputDecodeOrder
open RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000
variable {α β : Type*}
def indices (m : ℕ) : ℕ → ℕ → List ℕ
  | 0,_ => []
  | J+1,k => indices m J (k/m)++[k%m]
end ThreeSum.OutputDecodeOrder


