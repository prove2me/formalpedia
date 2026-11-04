-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalKeyRow
-- name    : Submission_ThreeSum_LightLocalKeyRow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:34:13.11647+00:00
-- url     : https://prove2.me/theorems/519a5912-3e0d-40fb-a4ee-4c72d2aed1b1
-- title:
--   Light Local Key Row
-- statement:
--   Definitions and structural lemmas for Light Local Key Row, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalKeyRow.lean

import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightLocalKeyRow
open Light LightSubsetAddress
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
def body (pFill pHashes pLinear : ℕ) : Stmt :=
  .set 6 (v 5 +' v 0) ;;
  .set 7 (v 6 +' v 2) ;;
  .set 8 (v 7 +' v 2) ;;
  .call pFill [v 5,v 0,k 0] 9 ;;
  .call pHashes [v 0,v 1,v 6,v 2,v 4,v 5,v 8] 9 ;;
  .call pHashes [v 0,v 1,v 7,v 2,v 3,v 5,v 8] 9 ;;
  .call pLinear [v 6,v 7,v 6,v 2,k 0 -' k 1] 9 ;;
  .set 0 (v 6)
def time (L n : ℕ) : ℕ := fillTime L+2*LightMaskHashes.time L n+LightArray.linearTime n+300
def space (free L n : ℕ) : ℕ := free+L+2*n+(L+1)
def word (L U : ℕ) : ℕ := 2*LightOneHot.word L U+2
structure Procs (P : Program) (pMain : ℕ) where
  pFill : ℕ
  pHashes : ℕ
  pPowers : ℕ
  pHash : ℕ
  pLinear : ℕ
  main : P[pMain]? = some (body pFill pHashes pLinear)
  fill : P[pFill]? = some fillBody
  hashes : P[pHashes]? = some (LightMaskHashes.body pPowers pHash)
  powers : P[pPowers]? = some powTableBody
  hash : P[pHash]? = some (LightOneHot.body pHash)
  linear : P[pLinear]? = some LightArray.linearBody
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1 2 5,fillBody,LightMaskHashes.body 3 4,
  powTableBody,LightOneHot.body 4,LightArray.linearBody]
def programProcs : Procs program 0 := ⟨1,2,3,4,5,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightLocalKeyRow


