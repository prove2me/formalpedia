-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTrimTest
-- name    : Submission_ThreeSum_LightTrimTest
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:26:17.166459+00:00
-- url     : https://prove2.me/theorems/0166519d-74f3-4127-b62b-f5f745e72df4
-- title:
--   Light Trim Test
-- statement:
--   Definitions and structural lemmas for Light Trim Test, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTrimTest.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTrimTest
open Light
def flag (overlap leftCount rightCount cap : ℕ) : ℕ :=
  if overlap=0 ∧ leftCount≤cap ∧ rightCount≤cap then 1 else 0
def body : Stmt :=
  .ite (v 0 =' k 0)
    (.ite (v 1 ≤' v 3)
      (.ite (v 2 ≤' v 3) (.set 0 (k 1)) (.set 0 (k 0)))
      (.set 0 (k 0)))
    (.set 0 (k 0))
def time : ℕ := 30
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightTrimTest


