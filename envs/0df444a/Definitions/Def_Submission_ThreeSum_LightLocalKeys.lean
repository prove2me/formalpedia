-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalKeys
-- name    : Submission_ThreeSum_LightLocalKeys
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:37:50.414903+00:00
-- url     : https://prove2.me/theorems/27ac6b06-5c77-4043-a347-23f4b961b525
-- title:
--   Light Local Keys
-- statement:
--   Definitions and structural lemmas for Light Local Keys, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalKeys.lean

import Definitions.Def_Submission_ThreeSum_LightLocalKeyRow
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightLocalKeys
open Light
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
def body (pRow pCopy : ℕ) : Stmt :=
  .for 7 (v 4) (
    .call pRow [v 0,v 1,v 2,v 3 +' v 7 *' (k 2 *' v 0),
      v 3 +' v 7 *' (k 2 *' v 0) +' v 0,v 6] 8 ;;
    .call pCopy [v 8,v 5 +' v 7 *' v 2,v 2] 9)
def time (L n rows : ℕ) : ℕ := rows*(LightLocalKeyRow.time L n+copyTime n+130)+20
def word (L U rows : ℕ) : ℕ := LightLocalKeyRow.word L U+rows+2*L+1
def Inv (μ : ℕ → ℤ) (L masks n maps rows dst free : ℕ)
    (mask : ℕ → ℕ) (wFalse wTrue : ℕ → ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r s : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [L,masks,n,maps,rows,dst,free,j,r,s],ν⟩ ∧
    (∀ k < j, ∀ i < n, ν (dst+k*n+i)=
      (OneHotMask.eval (wTrue k) (fun _ => 0) L (mask i) : ℤ)-
      (OneHotMask.eval (wFalse k) (fun _ => 0) L (mask i) : ℤ)) ∧ Kept μ ν dst
structure Procs (P : Program) (pMain : ℕ) where
  pRow : ℕ
  pCopy : ℕ
  main : P[pMain]? = some (body pRow pCopy)
  row : LightLocalKeyRow.Procs P pRow
  copy : P[pCopy]? = some copyBody
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1 7,LightLocalKeyRow.body 2 3 6,fillBody,
  LightMaskHashes.body 4 5,powTableBody,LightOneHot.body 5,
  LightArray.linearBody,copyBody]
def programProcs : Procs program 0 :=
  ⟨1,7,rfl,⟨2,3,4,5,6,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
end ThreeSum.LightLocalKeys


