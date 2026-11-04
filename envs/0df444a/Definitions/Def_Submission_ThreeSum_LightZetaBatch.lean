-- Prove2me | Definitions.Def_Submission_ThreeSum_LightZetaBatch
-- name    : Submission_ThreeSum_LightZetaBatch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:32:52.457252+00:00
-- url     : https://prove2.me/theorems/19d7284a-40d0-41d2-a185-75837a1f7049
-- title:
--   Light Zeta Batch
-- statement:
--   Definitions and structural lemmas for Light Zeta Batch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaBatch.lean

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightZetaBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.MaskDecode
variable {lim : Limits} {P : Program}
def body (pCell : ℕ) : Stmt :=
  .for 8 (v 2)
    (.call pCell [v 0,v 1,M (v 3 +' v 8),v 4,v 5,v 6,v 7] 9)
def time (L n : ℕ) : ℕ := n*(LightZetaCell.time L+40)+10
def values {L : ℕ} (μ : ℕ → ℤ) (dst : ℕ) (masks : List ℕ)
    (a : Fin L) (f : Finset (Fin L) → ℤ) (S : Finset (Fin L)) : ℤ :=
  if subsetMask S ∈ masks then Subset.zetaStep a f S else μ (dst+subsetRank S)
def Inv {L : ℕ} (μ : ℕ → ℤ) (cut cardinal maskBase src dst work : ℕ)
    (masks : List ℕ) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cardinal,masks.length,maskBase,a.val,src,dst,work,j,r],μ'⟩ ∧
    KeptBut μ μ' work dst (downsetCap L cut) ∧
    TableAt μ' dst cut (values μ dst (masks.take j) a f)
end ThreeSum.LightZetaBatch


