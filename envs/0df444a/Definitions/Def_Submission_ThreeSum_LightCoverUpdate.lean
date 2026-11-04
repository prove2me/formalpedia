-- Prove2me | Definitions.Def_Submission_ThreeSum_LightCoverUpdate
-- name    : Submission_ThreeSum_LightCoverUpdate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:21:47.082955+00:00
-- url     : https://prove2.me/theorems/850b1287-5656-4e92-86b8-55ef7461dfeb
-- title:
--   Light Cover Update
-- statement:
--   Definitions and structural lemmas for Light Cover Update, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverUpdate.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e

set_option autoImplicit false
namespace ThreeSum.LightCoverUpdate
open Light
def body : Stmt :=
  pass 3 (v 2) (v 1)
    (M (v 1 +' v 3) *' (k 1 -' M (v 0 +' v 3)))
def time (n : ℕ) : ℕ := 26*n+6
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightCoverUpdate


