-- Prove2me | Definitions.Def_Submission_ThreeSum_LightCoverGreedy
-- name    : Submission_ThreeSum_LightCoverGreedy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:32:28.119912+00:00
-- url     : https://prove2.me/theorems/e36d22ab-1dd8-42a5-a646-0c90be969bfe
-- title:
--   Light Cover Greedy
-- statement:
--   Definitions and structural lemmas for Light Cover Greedy, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverGreedy.lean

import Definitions.Def_Submission_ThreeSum_LightCoverSelect
import Definitions.Def_Submission_ThreeSum_LightCoverUpdate
import Definitions.Def_Submission_ThreeSum_BooleanGreedy
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
namespace ThreeSum.LightCoverGreedy
open Light BooleanGreedy
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000
def out (activePtr rows cols : ℕ) : ℕ := activePtr+cols+rows
def total (rows cols rounds : ℕ) : ℕ := cols+rows+rounds
def roundBody (pSelect pUpdate : ℕ) : Stmt :=
  .call pSelect [v 0,v 1,v 5,v 2,v 3] 8 ;;
  .store (v 6 +' v 7) (v 8) ;;
  .call pUpdate [v 0 +' v 8 *' v 3,v 1,v 3] 9
def body (pFill pSelect pUpdate : ℕ) : Stmt :=
  .set 5 (v 1 +' v 3) ;;
  .set 6 (v 5 +' v 2) ;;
  .call pFill [v 1,v 3,k 1] 9 ;;
  .for 7 (v 4) (roundBody pSelect pUpdate) ;;
  .set 0 (v 6)
def roundTime (rows cols : ℕ) : ℕ :=
  LightCoverSelect.time rows cols+LightCoverUpdate.time cols+200
def time (rows cols rounds : ℕ) : ℕ :=
  fillTime cols+rounds*(roundTime rows cols+8)+100
def Inv (μ : ℕ → ℤ) (matrix : ℕ → ℕ → ℕ)
    (src activePtr rows cols rounds i : ℕ) (σ : State) : Prop :=
  ∃ (r v : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [src,activePtr,rows,cols,rounds,activePtr+cols,out activePtr rows cols,i,r,v],μ'⟩ ∧
    (∀ j < cols, μ' (activePtr+j) = (active matrix rows cols i j : ℤ)) ∧
    Seg μ' (out activePtr rows cols) ((choices matrix rows cols i).map (fun x : ℕ => (x : ℤ))) ∧
    SameOutside μ μ' activePtr (total rows cols rounds)
structure Procs (P : Program) (pMain : ℕ) where
  pFill : ℕ
  pSelect : ℕ
  pUpdate : ℕ
  fill : P[pFill]? = some fillBody
  select : LightCoverSelect.Procs P pSelect
  update : P[pUpdate]? = some LightCoverUpdate.body
  main : P[pMain]? = some (body pFill pSelect pUpdate)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 2 6,fillBody,LightCoverSelect.body 3 5,LightCoverScores.body 4,
    LightBooleanDot.body,LightMinimum.body,LightCoverUpdate.body]
def programProcs : Procs program 0 :=
  ⟨1,2,6,rfl,⟨3,4,5,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩
end ThreeSum.LightCoverGreedy


