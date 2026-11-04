-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingSuffixBatch
-- name    : Submission_ThreeSum_LightReportingSuffixBatch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:23:22.800607+00:00
-- url     : https://prove2.me/theorems/20389e9c-e787-41bc-b638-8c90b1f06d58
-- title:
--   Light Reporting Suffix Batch
-- statement:
--   Definitions and structural lemmas for Light Reporting Suffix Batch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixBatch.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightReportingSuffixBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell ThreeSum.MaskDecode
open ReportingHostSuffix
variable {lim : Limits} {P : Program}
def body (pCell : ℕ) : Stmt :=
  .for 16 (v 10)
    (.call pCell [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 9,M (v 11 +' v 16),
      v 8,v 12,v 13,v 14,v 15] 17)
def time (W V n : ℕ) : ℕ := n*(LightReportingSuffixCell.time W V+65)+20
def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (sourceCut boxCut stage cardinal maskBase baseL baseR dst work : ℕ)
    (masks : List ℕ) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,sourceCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      V,2^offset,cardinal,masks.length,maskBase,baseL,baseR,dst,work,j,r],μ'⟩ ∧
    KeptBut μ μ' work dst (downsetCap V boxCut) ∧
    TableAt μ' dst boxCut
      (LightSignedLeafBatch.values μ dst (masks.take j) (leafWeight hfit f g stage preL preR))
end ThreeSum.LightReportingSuffixBatch


