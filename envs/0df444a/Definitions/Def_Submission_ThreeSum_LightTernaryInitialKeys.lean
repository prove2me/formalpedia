-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryInitialKeys
-- name    : Submission_ThreeSum_LightTernaryInitialKeys
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:21:37.781968+00:00
-- url     : https://prove2.me/theorems/12fea8a1-c062-4902-a593-aa51b23ed2de
-- title:
--   Light Ternary Initial Keys
-- statement:
--   Definitions and structural lemmas for Light Ternary Initial Keys, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryInitialKeys.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryInitialKeys
open Light
set_option maxHeartbeats 2000000
def body : Stmt :=
  .call 0 [v 0,v 1,k 0] 6 ;;
  .call 0 [v 2,v 3,k 0] 6 ;;
  .call 0 [v 4,v 5,k 0] 6 ;;
  .set 0 (k 0)
def program : Program :=[fillBody,body]
def time (nB nC nO : ℕ) : ℕ :=fillTime nB+fillTime nC+fillTime nO+100
end ThreeSum.LightTernaryInitialKeys


