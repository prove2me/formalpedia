-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
-- name    : Submission_ThreeSum_LightTernaryMomentAccumulate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:17.209056+00:00
-- url     : https://prove2.me/theorems/c7c9c86c-2ca6-48c0-8afd-dcb848041391
-- title:
--   Light Ternary Moment Accumulate
-- statement:
--   Definitions and structural lemmas for Light Ternary Moment Accumulate, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentAccumulate.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e

set_option autoImplicit false
namespace ThreeSum.LightTernaryMomentAccumulate
open Light
def body : Stmt := pass 3 (v 2) (v 0)
  (M (v 0 +' v 3) +' M (v 1 +' v 3))
def time (count : ℕ) : ℕ := 24*count+10
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body,fillBody]
end ThreeSum.LightTernaryMomentAccumulate


