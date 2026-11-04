-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSwitch
-- name    : Submission_ThreeSum_LightSwitch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:04:30.814747+00:00
-- url     : https://prove2.me/theorems/ec3650ee-8fa5-475c-9d0b-859c30bef008
-- title:
--   Light Switch
-- statement:
--   Definitions and structural lemmas for Light Switch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitch.lean

import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
def test : Cond :=
  (k 10 *' (v 0 -' v 1) *'
    (v 3 *' (k 799 *' v 2 *' v 2 +' v 3 *' (k 72 *' v 2 +' k 24 *' v 3)))) <'
    ((k 291 *' v 0 +' k 1000 *' v 1) *' v 2 *' v 2 *' v 2)
def body : Stmt :=
  .set 3 (k 0) ;;
  .while test (.set 3 (v 3 +' k 1)) ;;
  .set 0 (v 3)
def time (r : ℕ) : ℕ := 100*(r+1)+50
variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J j r q d : ℕ}
def program : Program := [body]
end ThreeSum.LightSwitch


