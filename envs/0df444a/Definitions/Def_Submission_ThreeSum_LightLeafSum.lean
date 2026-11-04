-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLeafSum
-- name    : Submission_ThreeSum_LightLeafSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:52:16.992215+00:00
-- url     : https://prove2.me/theorems/fa32b9ea-a745-44a2-86de-7f9489bffde1
-- title:
--   Light Leaf Sum
-- statement:
--   Definitions and structural lemmas for Light Leaf Sum, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLeafSum.lean

import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightLeafSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def term {W : ℕ} (Q preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (U : Finset (Fin W)) : ℤ := SignedLeaf.value f g stage preL preR (Q \ U)
def partialSum {W : ℕ} (Q preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin W))) (j : ℕ) : ℤ :=
  ((missing.map (term Q preL preR f g stage)).take j).sum
def roundBody (pLeaf : ℕ) : Stmt :=
  .call pLeaf [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7 -' v 9,
    v 8 -' M (v 11 +' v 16),v 12,v 13,v 14] 17 ;;
  .set 15 (v 15 +' v 17)
def body (pLeaf : ℕ) : Stmt :=
  .set 15 (k 0) ;;
  .for 16 (v 10) (roundBody pLeaf) ;;
  .set 0 (v 15)
def time (W n : ℕ) : ℕ := n*(LightSignedLeaf.time W+60)+40
def Inv {W : ℕ} (μ : ℕ → ℤ) (Q preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ) (stage : ℕ) (missing : List (Finset (Fin W)))
    (cut t maskBase baseL baseR work j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      Q.card,subsetMask Q,t,missing.length,maskBase,baseL,baseR,work,
      partialSum Q preL preR f g stage missing j,j,r],μ'⟩ ∧ Kept μ μ' work
def program : Program :=
  [body 1,LightSignedLeaf.body 2 13,LightStageLookup.body 3 4,
    LightDownsetSize.body 5 12,LightDownsetAddress.body 5 12,
    LightSubsetSetup.body 6 10 11,buildBody 7 8,fillBody,rowBody 9,
    LightArray.linearBody,powTableBody,rankBody 11,LightSubsetOffset.body,LightSign.body]
end ThreeSum.LightLeafSum


