-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
-- name    : Submission_ThreeSum_LightTernaryOriginalRequester
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:22:50.821638+00:00
-- url     : https://prove2.me/theorems/00d8dbfe-0d34-4237-93e4-098c3e30077b
-- title:
--   Light Ternary Original Requester
-- statement:
--   Definitions and structural lemmas for Light Ternary Original Requester, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryOriginalRequester.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryCarryApply
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightTernaryOriginalRequester
open Light TernarySignedDigits TernarySignedReduction
def body (pRow pApply : ℕ) : Stmt :=
  .call pRow [v 0,v 1,k 1,v 3,v 2,v 4,v 6,k 1,k 1] 7 ;;
  .call pApply [v 4,v 5,v 3,v 2] 0
def time (J U : ℕ) : ℕ :=
  LightTernarySignedRow.time J (3*U)+LightTernaryCarryApply.time J+80
structure Procs (P : Program) (pMain : ℕ) where
  pRow : ℕ
  pApply : ℕ
  pLinear : ℕ
  row : LightTernarySignedRow.Procs P pRow
  correction : P[pApply]?=some (LightTernaryCarryApply.body pLinear)
  linear : P[pLinear]?=some LightArray.linearBody
  main : P[pMain]?=some (body pRow pApply)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 4,LightTernarySignedRow.body 2,LightOutputDecodeDigits.body 3,
    LightOutputDecodeDivide.body,LightTernaryCarryApply.body 5,LightArray.linearBody]
def procs : Procs program 0 where
  pRow := 1
  pApply := 4
  pLinear := 5
  row := ⟨2,3,rfl,rfl,rfl⟩
  correction := rfl
  linear := rfl
  main := rfl
end ThreeSum.LightTernaryOriginalRequester


