-- Prove2me | Definitions.Def_Submission_ThreeSum_LightQueryWeights
-- name    : Submission_ThreeSum_LightQueryWeights
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:47:38.776201+00:00
-- url     : https://prove2.me/theorems/bb230df2-76d0-4447-a723-fd45cb1aa6b6
-- title:
--   Light Query Weights
-- statement:
--   Definitions and structural lemmas for Light Query Weights, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryWeights.lean

import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightQueryWeights
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}
def roundBody (pErase : ℕ) : Stmt :=
  .call pErase [v 0,v 6,v 1,v 0,v 3] 7 ;;
  .ite (v 7 <' v 1)
    (.store (v 2 +' v 5) (M (v 3 +' v 6)) ;; .set 5 (v 5 +' k 1))
    .skip
def body (pPowers pErase : ℕ) : Stmt :=
  .call pPowers [v 3,v 0 +' k 1,k 2] 4 ;;
  .set 5 (k 0) ;;
  .for 6 (v 0) (roundBody pErase) ;;
  .set 0 (v 5)
def time (W : ℕ) : ℕ := powTableTime (W+1)+W*(LightMaskErase.time W+100)+100
def Inv {W : ℕ} (μ : ℕ → ℤ) (Q : Finset (Fin W))
    (dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,subsetMask Q,dst,work,powRet,(positions Q j).length,j,r],μ'⟩ ∧
    SegN μ' dst (selectedPowers Q j) ∧ Powers μ' work W ∧
    KeptBut μ μ' work dst W
def program : Program := [body 1 2,powTableBody,LightMaskErase.body 2]
end ThreeSum.LightQueryWeights


