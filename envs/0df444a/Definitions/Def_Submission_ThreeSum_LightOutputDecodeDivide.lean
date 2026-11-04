-- Prove2me | Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
-- name    : Submission_ThreeSum_LightOutputDecodeDivide
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:38:47.557257+00:00
-- url     : https://prove2.me/theorems/df95d8eb-fddd-4955-b3e5-6337d40ecd95
-- title:
--   Light Output Decode Divide
-- statement:
--   Definitions and structural lemmas for Light Output Decode Divide, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOutputDecodeDivide.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
namespace ThreeSum.LightOutputDecodeDivide
open Light Light.Emod
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
abbrev Quotient : ℕ := 6
def reduceRound : Stmt :=
  .set Count (v Count -' k 1) ;;
  .set Quotient (k 2 *' v Quotient) ;;
  .ite (M (v Free +' v Count) ≤' v Rest)
    (.set Rest (v Rest -' M (v Free +' v Count)) ;;
      .set Quotient (v Quotient +' k 1)) .skip
def reduce : Stmt := .while (k 0 <' v Count) reduceRound
def body : Stmt :=
  .set Rest (v Arg) ;;
  .set Count (k 0) ;;
  .set Mult (v Modulus) ;;
  emodTable ;;
  .set Quotient (k 0) ;;
  reduce ;;
  .set Arg (v Quotient)
def time (a Mo : ℕ) : ℕ := 80*emodRounds a Mo+100
def budget (V : ℕ) : ℕ := 100*(Nat.log 2 (V+1)+2)
variable {lim : Limits} {P : Program} {d : ℕ} {μ ν : ℕ → ℤ} {a Mo V fr : ℕ}
def program : Program := [body]
end ThreeSum.LightOutputDecodeDivide


