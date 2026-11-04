-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryCarryApply
-- name    : Submission_ThreeSum_LightTernaryCarryApply
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:19:19.02695+00:00
-- url     : https://prove2.me/theorems/169aae83-4527-439e-b265-3884afcd5637
-- title:
--   Light Ternary Carry Apply
-- statement:
--   Definitions and structural lemmas for Light Ternary Carry Apply, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryApply.lean

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightTernaryCarryApply
open Light TernarySignedDigits TernarySignedReduction TernarySignedModes
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
def body (pLinear : ℕ) : Stmt :=
  .call pLinear [v 0,v 1,v 0,v 2,k 0 -' v 3] 4 ;;
  .call pLinear [v 0,v 1 +' k 1,v 0,v 2,k 1] 0
def time (J : ℕ) : ℕ := 2*LightArray.linearTime J+60
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,LightArray.linearBody]
end ThreeSum.LightTernaryCarryApply


