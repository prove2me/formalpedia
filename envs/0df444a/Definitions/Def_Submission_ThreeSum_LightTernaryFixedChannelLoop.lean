-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryFixedChannelLoop
-- name    : Submission_ThreeSum_LightTernaryFixedChannelLoop
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:49:58.318228+00:00
-- url     : https://prove2.me/theorems/2c150d75-3c44-49b1-be0b-56132c38df08
-- title:
--   Light Ternary Fixed Channel Loop
-- statement:
--   Definitions and structural lemmas for Light Ternary Fixed Channel Loop, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFixedChannelLoop.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
namespace ThreeSum.LightTernaryFixedChannelLoop
open Light
set_option maxHeartbeats 1500000
abbrev Channel := ℕ×ℕ
def arguments (arity : ℕ) : List Expr := LightTernaryMomentChannelStep.callArgs (List.range arity)
def body (steps : List Channel) (entry : Channel→ℕ) (arity : ℕ) : Stmt :=
  match steps with
  | [] => .skip
  | c::cs => .call (entry c) (arguments arity) arity ;; body cs entry arity
def time (steps : List Channel) (cost : Channel→ℕ) (arity : ℕ) : ℕ :=
  match steps with
  | [] => 0
  | c::cs => arity+2+cost c+time cs cost arity
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightTernaryFixedChannelLoop


