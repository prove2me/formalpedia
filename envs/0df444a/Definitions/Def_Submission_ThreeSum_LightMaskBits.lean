-- Prove2me | Definitions.Def_Submission_ThreeSum_LightMaskBits
-- name    : Submission_ThreeSum_LightMaskBits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:29:44.800793+00:00
-- url     : https://prove2.me/theorems/2c8b15ea-324b-4970-a878-faa0ce5fb9b3
-- title:
--   Light Mask Bits
-- statement:
--   Definitions and structural lemmas for Light Mask Bits, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskBits.lean

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightMaskBits
open Light LightSubsetAddress MaskErase
def bit (L m j : ℕ) : ℕ := if eraseMask L j m = m then 0 else 1
def loopBody (pErase : ℕ) : Stmt :=
  .for 4 (v 0) (
    .call pErase [v 0,v 4,v 1,v 0,v 3] 5 ;;
    .ite (v 5 =' v 1) (.store (v 2 +' v 4) (k 0)) (.store (v 2 +' v 4) (k 1)))
def body (pPowers pErase : ℕ) : Stmt :=
  .call pPowers [v 3,v 0 +' k 1,k 2] 5 ;;
  loopBody pErase
def time (L : ℕ) : ℕ := powTableTime (L+1)+L*(LightMaskErase.time L+80)+50
def Inv (μ : ℕ → ℤ) (L m dst work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [L,m,dst,work,i,r],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (bit L m j : ℤ)) ∧ Powers μ' work L ∧
    KeptBut μ μ' work dst L
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1 2,powTableBody,LightMaskErase.body 2]
end ThreeSum.LightMaskBits


