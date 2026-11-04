-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSwitchDepth
-- name    : Submission_ThreeSum_LightSwitchDepth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:08:28.766274+00:00
-- url     : https://prove2.me/theorems/27a22d6f-db4c-4830-b46d-f33d6653ee54
-- title:
--   Light Switch Depth
-- statement:
--   Definitions and structural lemmas for Light Switch Depth, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchDepth.lean

import Definitions.Def_Submission_ThreeSum_LightSwitch
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSwitchDepth
open Light
def depth (J : ℕ) : ℕ := 13*J/20
def body (pDiv : ℕ) : Stmt :=
  .call pDiv [k 13 *' v 0,k 20] 1 ;;
  .set 0 (v 1)
def time (J : ℕ) : ℕ := LightSmallDivide.time (13*J) 20+50
def word (J : ℕ) : ℕ := 13*J+22
variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J d : ℕ}
def program : Program := [body 1,LightSmallDivide.body]
end ThreeSum.LightSwitchDepth


