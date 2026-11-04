-- Prove2me | Definitions.Def_Submission_ThreeSum_LightArray
-- name    : Submission_ThreeSum_LightArray
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:17:35.408501+00:00
-- url     : https://prove2.me/theorems/5a4dcb44-05f6-40e5-b56d-4d07e5e62140
-- title:
--   Light Array
-- statement:
--   Definitions and structural lemmas for Light Array, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightArray.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e

set_option autoImplicit false
namespace ThreeSum.LightArray
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
def SourceSafe (src dst n : ℕ) : Prop := src = dst ∨ Apart src n dst n
def linearBody : Stmt :=
  pass 5 (v 3) (v 2) (M (v 0 +' v 5) +' v 4 *' M (v 1 +' v 5))
def linearTime (n : ℕ) : ℕ := 23 * n + 6
end ThreeSum.LightArray


