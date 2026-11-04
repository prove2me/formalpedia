-- Prove2me | Definitions.Def_Submission_ThreeSum_LightNatPower
-- name    : Submission_ThreeSum_LightNatPower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:50:48.939214+00:00
-- url     : https://prove2.me/theorems/001dfce5-7747-4e90-8fb8-e21cc7db5435
-- title:
--   Light Nat Power
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNatPower.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightNatPower
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
def body : Stmt :=
  .set 2 (k 1) ;;
  .for 3 (v 1) (.set 2 (v 2 *' v 0)) ;;
  .set 0 (v 2)
def time (e : ℕ) : ℕ := 20*e+20
def program : Program := [body]
end ThreeSum.LightNatPower


