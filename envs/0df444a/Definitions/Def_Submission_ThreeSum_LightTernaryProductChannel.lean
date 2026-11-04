-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryProductChannel
-- name    : Submission_ThreeSum_LightTernaryProductChannel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:41:47.56328+00:00
-- url     : https://prove2.me/theorems/d9d1b4a1-6610-418f-b536-3f52dc263506
-- title:
--   Light Ternary Product Channel
-- statement:
--   Definitions and structural lemmas for Light Ternary Product Channel, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryProductChannel.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e

set_option autoImplicit false
namespace ThreeSum.LightTernaryProductChannel
open Light TernaryWeightChannels
def body : Stmt := pass 6 (v 1) (v 5)
  (M (v 0 +' v 6 *' v 2 +' v 3) *' M (v 0 +' v 6 *' v 2 +' v 4))
def time (n : ℕ) : ℕ := 40*n+10
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightTernaryProductChannel


