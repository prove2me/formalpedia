-- Prove2me | Definitions.Def_Submission_ThreeSum_LightMaskBitTable
-- name    : Submission_ThreeSum_LightMaskBitTable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:46:09.269186+00:00
-- url     : https://prove2.me/theorems/292390f4-aead-4164-8732-c6c8376cb471
-- title:
--   Light Mask Bit Table
-- statement:
--   Definitions and structural lemmas for Light Mask Bit Table, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskBitTable.lean

import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightMaskBitTable
open Light
set_option maxHeartbeats 1000000
def body (pBits : ℕ) : Stmt :=
  .for 5 (v 3) (.call pBits [v 0,M (v 1 +' v 5),v 2 +' v 5 *' v 0,v 4] 6)
def time (L n : ℕ) : ℕ := n*(LightMaskBits.time L+70)+6
def Inv (μ : ℕ → ℤ) (mask : ℕ → ℕ)
    (L masks dst n work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [L,masks,dst,n,work,i,r],μ'⟩ ∧
    (∀ j < i, ∀ a < L, μ' (dst+j*L+a) = (LightMaskBits.bit L (mask j) a : ℤ)) ∧
    KeptBut μ μ' work dst (n*L)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,LightMaskBits.body 2 3,powTableBody,LightMaskErase.body 3]
end ThreeSum.LightMaskBitTable


