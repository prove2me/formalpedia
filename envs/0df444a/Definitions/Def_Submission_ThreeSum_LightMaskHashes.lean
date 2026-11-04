-- Prove2me | Definitions.Def_Submission_ThreeSum_LightMaskHashes
-- name    : Submission_ThreeSum_LightMaskHashes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:30:50.264488+00:00
-- url     : https://prove2.me/theorems/8e91e759-b300-405d-a6c8-321bd31bca7a
-- title:
--   Light Mask Hashes
-- statement:
--   Definitions and structural lemmas for Light Mask Hashes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskHashes.lean

import Definitions.Def_Submission_ThreeSum_LightOneHot
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightMaskHashes
open Light LightSubsetAddress
set_option maxHeartbeats 1000000
def loopBody (pHash : ℕ) : Stmt :=
  .for 7 (v 3) (
    .call pHash [v 0,M (v 1 +' v 7),v 0,v 6,v 4,v 5] 8 ;;
    .store (v 2 +' v 7) (v 8))
def body (pPowers pHash : ℕ) : Stmt :=
  .call pPowers [v 6,v 0 +' k 1,k 2] 8 ;;
  loopBody pHash
def time (L n : ℕ) : ℕ := powTableTime (L+1)+n*(LightOneHot.time L+70)+50
def Inv (μ : ℕ → ℤ) (mask w0 w1 : ℕ → ℕ)
    (L masks dst n src0 src1 work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,masks,dst,n,src0,src1,work,i,r],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (OneHotMask.eval w0 w1 L (mask j) : ℤ)) ∧
    Powers μ' work L ∧ KeptBut μ μ' work dst n
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1 2,powTableBody,LightOneHot.body 2]
end ThreeSum.LightMaskHashes


