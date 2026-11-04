-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSignedLeafBatch
-- name    : Submission_ThreeSum_LightSignedLeafBatch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:57:29.232273+00:00
-- url     : https://prove2.me/theorems/b416df99-b6e2-4835-ae8f-85485747dd24
-- title:
--   Light Signed Leaf Batch
-- statement:
--   Definitions and structural lemmas for Light Signed Leaf Batch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafBatch.lean

import Definitions.Def_Submission_ThreeSum_LightSignedLeafCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSignedLeafBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell ThreeSum.MaskDecode
variable {lim : Limits} {P : Program}
def body (pCell : ℕ) : Stmt :=
  .for 14 (v 8)
    (.call pCell [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,M (v 9 +' v 14),
      v 10,v 11,v 12,v 13] 15)
def time (W n : ℕ) : ℕ := n*(LightSignedLeafCell.time W+55)+20
def values {W : ℕ} (μ : ℕ → ℤ) (dst : ℕ) (masks : List ℕ)
    (weight : Finset (Fin W) → ℤ) (S : Finset (Fin W)) : ℤ :=
  if subsetMask S ∈ masks then weight S else μ (dst+subsetRank S)
def Inv {W : ℕ} (μ : ℕ → ℤ) (sourceCut boxCut stage cardinal maskBase baseL baseR dst work : ℕ)
    (masks : List ℕ) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,sourceCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      cardinal,masks.length,maskBase,baseL,baseR,dst,work,j,r],μ'⟩ ∧
    KeptBut μ μ' work dst (downsetCap W boxCut) ∧
    TableAt μ' dst boxCut
      (values μ dst (masks.take j) (SignedLeaf.value f g stage preL preR))
end ThreeSum.LightSignedLeafBatch


