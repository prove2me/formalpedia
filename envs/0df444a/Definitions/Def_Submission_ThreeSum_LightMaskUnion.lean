-- Prove2me | Definitions.Def_Submission_ThreeSum_LightMaskUnion
-- name    : Submission_ThreeSum_LightMaskUnion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:30:47.337454+00:00
-- url     : https://prove2.me/theorems/2f3cc373-ba32-4a06-b4b4-2185be19a2c4
-- title:
--   Light Mask Union
-- statement:
--   Definitions and structural lemmas for Light Mask Union, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskUnion.lean

import Definitions.Def_Submission_ThreeSum_MaskUnion
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightMaskUnion
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open MaskUnion
variable {lim : Limits} {P : Program}
def roundBody (pErase : ℕ) : Stmt :=
  .call pErase [v 0,v 9,v 3,v 0,v 5] 10 ;;
  .call pErase [v 0,v 9,v 2,v 0,v 5] 11 ;;
  .ite (v 10 <' v 3)
    (.ite (v 11 <' v 2) .skip
      (.set 7 (v 7 +' k 1) ;; .set 8 (v 8 +' M (v 5 +' v 9))))
    .skip
def body (pPowers pErase : ℕ) : Stmt :=
  .call pPowers [v 5,v 0 +' k 1,k 2] 6 ;;
  .set 7 (v 1) ;;
  .set 8 (v 2) ;;
  .for 9 (v 0) (roundBody pErase) ;;
  .store (v 4) (v 7) ;;
  .set 0 (v 8)
def time (W : ℕ) : ℕ :=
  powTableTime (W+1)+W*(2*LightMaskErase.time W+180)+200
def Inv {W : ℕ} (μ : ℕ → ℤ) (A B : Finset (Fin W))
    (dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ eB eA : ℤ,
    σ = ⟨frame [W,A.card,subsetMask A,subsetMask B,dst,work,powRet,
      (scanSet A B j).card,subsetMask (scanSet A B j),j,eB,eA],μ⟩
def program : Program := [body 1 2,powTableBody,LightMaskErase.body 2]
end ThreeSum.LightMaskUnion


