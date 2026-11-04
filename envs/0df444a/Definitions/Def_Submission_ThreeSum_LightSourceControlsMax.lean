-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceControlsMax
-- name    : Submission_ThreeSum_LightSourceControlsMax
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:05:32.558259+00:00
-- url     : https://prove2.me/theorems/baea27c0-de02-48da-9651-4293222f73bf
-- title:
--   Light Source Controls Max
-- statement:
--   Definitions and structural lemmas for Light Source Controls Max, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceControlsMax.lean

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSourceControlsMax
open Light
def body : Stmt := .ite (v 0 <' v 1) (.set 0 (v 1)) (.set 0 (v 0))
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightSourceControlsMax


