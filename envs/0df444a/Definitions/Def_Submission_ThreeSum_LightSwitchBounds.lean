-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSwitchBounds
-- name    : Submission_ThreeSum_LightSwitchBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:02:42.783349+00:00
-- url     : https://prove2.me/theorems/73bd5b12-e959-4449-8774-56dea1e5861f
-- title:
--   Light Switch Bounds
-- statement:
--   Definitions and structural lemmas for Light Switch Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitchBounds.lean

import Definitions.Def_Submission_ThreeSum_Switch
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
set_option autoImplicit false
namespace ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
def left (J j r : ℕ) : ℕ := (291*J+1000*j)*r*r*r
def cubic (r q : ℕ) : ℕ := q*(799*r*r+q*(72*r+24*q))
def factor (J j : ℕ) : ℕ := 10*(J-j)
def word (J r : ℕ) : ℕ := (J+r+1001)^64
end ThreeSum.LightSwitch


