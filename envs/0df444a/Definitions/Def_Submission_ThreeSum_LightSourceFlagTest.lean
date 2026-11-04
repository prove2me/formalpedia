-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceFlagTest
-- name    : Submission_ThreeSum_LightSourceFlagTest
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:21:20.446137+00:00
-- url     : https://prove2.me/theorems/3907d25d-9e67-49ee-a2c0-b5f65ece6b6e
-- title:
--   Light Source Flag Test
-- statement:
--   Definitions and structural lemmas for Light Source Flag Test, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceFlagTest.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSourceFlagTest
open Light
def flag (card required count cap : ℕ) : ℕ :=
  if card=required ∧ count≤cap then 1 else 0
def body : Stmt :=
  .ite (v 0 =' v 1)
    (.ite (v 2 ≤' v 3) (.set 0 (k 1)) (.set 0 (k 0)))
    (.set 0 (k 0))
def time : ℕ := 25
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightSourceFlagTest


