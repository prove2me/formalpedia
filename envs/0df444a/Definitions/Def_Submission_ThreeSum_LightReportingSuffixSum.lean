-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingSuffixSum
-- name    : Submission_ThreeSum_LightReportingSuffixSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:23:29.797514+00:00
-- url     : https://prove2.me/theorems/99c624dd-0cc1-41ca-b2ca-bced9944d9a4
-- title:
--   Light Reporting Suffix Sum
-- statement:
--   Definitions and structural lemmas for Light Reporting Suffix Sum, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixSum.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Definitions.Def_Submission_ThreeSum_LightLeafSum
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingSuffixSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
variable {lim : Limits} {P : Program}
def term {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (U : Finset (Fin V)) : ℤ := leafWeight hfit f g stage preL preR (Q \ U)
def partialSum {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin V))) (j : ℕ) : ℤ :=
  ((missing.map (term hfit Q preL preR f g stage)).take j).sum
def roundBody (pLeaf : ℕ) : Stmt :=
  .set 19 ((v 10 -' M (v 13 +' v 18)) *' v 8) ;;
  .call pLeaf [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 9 -' v 11,v 19,v 14,v 15,v 16] 20 ;;
  .set 17 (v 17 +' v 20)
def body (pLeaf : ℕ) : Stmt :=
  .set 17 (k 0) ;;
  .for 18 (v 12) (roundBody pLeaf) ;;
  .set 0 (v 17)
def time (W n : ℕ) : ℕ := n*(LightSignedLeafGeneral.time W+100)+40
def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (Q : Finset (Fin V)) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin V)))
    (cut t maskBase baseL baseR work j : ℕ) (σ : State) : Prop :=
  ∃ (mask r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      V,2^offset,Q.card,subsetMask Q,t,missing.length,maskBase,baseL,baseR,work,
      partialSum hfit Q preL preR f g stage missing j,j,mask,r],μ'⟩ ∧ Kept μ μ' work
end ThreeSum.LightReportingSuffixSum


