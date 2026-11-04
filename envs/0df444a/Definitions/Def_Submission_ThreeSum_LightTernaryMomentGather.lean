-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryMomentGather
-- name    : Submission_ThreeSum_LightTernaryMomentGather
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:21:56.307437+00:00
-- url     : https://prove2.me/theorems/dd471588-f612-4d5b-b900-4080408e5cca
-- title:
--   Light Ternary Moment Gather
-- statement:
--   Definitions and structural lemmas for Light Ternary Moment Gather, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentGather.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e

set_option autoImplicit false
namespace ThreeSum.LightTernaryMomentGather
open Light
def body : Stmt := pass 5 (v 4) (v 3) (M (v 0 +' v 5 *' v 1 +' v 2))
def time (terms : ℕ) : ℕ := 30*terms+10
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightTernaryMomentGather


