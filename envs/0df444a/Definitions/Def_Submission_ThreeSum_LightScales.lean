-- Prove2me | Definitions.Def_Submission_ThreeSum_LightScales
-- name    : Submission_ThreeSum_LightScales
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:54:00.824267+00:00
-- url     : https://prove2.me/theorems/5dcf81ed-0b87-4caa-accf-10cbe9f72bd5
-- title:
--   Light Scales
-- statement:
--   Definitions and structural lemmas for Light Scales, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}
def values (n : ℕ) : List ℤ :=
  [inputBits n,microHalf (inputBits n),muZero n,blockCount (inputBits n),mu n]
def body (pLog pCube pHalf pDiv : ℕ) : Stmt :=
  .call pLog [v 0] 2 ;;
  .call pCube [v 2 +' k 1] 3 ;;
  .call pHalf [v 3] 4 ;;
  .set 5 (v 4 -' k 1) ;;
  .set 6 (k 2 *' v 5) ;;
  .call pDiv [v 2,k 100 *' v 6] 7 ;;
  .set 8 (k 20 *' v 7) ;;
  .set 9 (v 8 *' v 6) ;;
  .store (v 1) (v 2) ;;
  .store (v 1 +' k 1) (v 5) ;;
  .store (v 1 +' k 2) (v 6) ;;
  .store (v 1 +' k 3) (v 8) ;;
  .store (v 1 +' k 4) (v 9) ;;
  .set 0 (v 9)
def time (n : ℕ) : ℕ := log2Time n + cbrtCeilTime (inputBits n+1) +
  halfTime (cbrtLeast (inputBits n+1)) +
  LightSmallDivide.time (inputBits n) (100*muZero n)+200
def program : Program := [body 1 2 3 4,log2Body,cbrtCeilBody,halfBody,LightSmallDivide.body]
structure Procs (P : Program) (pMain : ℕ) where
  pLog : ℕ
  pCube : ℕ
  pHalf : ℕ
  pDiv : ℕ
  main : P[pMain]? = some (body pLog pCube pHalf pDiv)
  log : P[pLog]? = some log2Body
  cube : P[pCube]? = some cbrtCeilBody
  half : P[pHalf]? = some halfBody
  divide : P[pDiv]? = some LightSmallDivide.body
end ThreeSum.LightScales


