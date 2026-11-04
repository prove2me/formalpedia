-- Prove2me | Definitions.Def_Submission_ThreeSum_LightScaleArray
-- name    : Submission_ThreeSum_LightScaleArray
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:30.355288+00:00
-- url     : https://prove2.me/theorems/e7ca4fba-eeef-451e-be87-395fa2e34011
-- title:
--   Light Scale Array
-- statement:
--   Definitions and structural lemmas for Light Scale Array, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScaleArray.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e

set_option autoImplicit false
namespace ThreeSum.LightScaleArray
open Light ThreeSum.LightArray
variable {lim : Limits} {P : Program} {d : ℕ}
def body : Stmt := pass 4 (v 2) (v 1) (v 3 *' M (v 0 +' v 4))
def time (n : ℕ) : ℕ := 18*n+6
def program : Program := [body]
end ThreeSum.LightScaleArray


