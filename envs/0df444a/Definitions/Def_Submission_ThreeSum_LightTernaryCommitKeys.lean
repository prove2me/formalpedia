-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryCommitKeys
-- name    : Submission_ThreeSum_LightTernaryCommitKeys
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:21:36.917729+00:00
-- url     : https://prove2.me/theorems/061c9563-7991-4954-b9b4-0844d9d224ff
-- title:
--   Light Ternary Commit Keys
-- statement:
--   Definitions and structural lemmas for Light Ternary Commit Keys, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCommitKeys.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryCommitKeys
open Light
set_option maxHeartbeats 2000000
def body : Stmt :=
  .call 0 [v 0,v 1,v 2] 9 ;;
  .call 0 [v 3,v 4,v 5] 9 ;;
  .call 0 [v 6,v 7,v 8] 9 ;;
  .set 0 (k 0)
def program : Program :=[copyBody,body]
def time (nB nC nO : ℕ) : ℕ :=copyTime nB+copyTime nC+copyTime nO+100
end ThreeSum.LightTernaryCommitKeys


