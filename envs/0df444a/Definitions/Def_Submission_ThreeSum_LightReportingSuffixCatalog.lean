-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalog
-- name    : Submission_ThreeSum_LightReportingSuffixCatalog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:34:08.450196+00:00
-- url     : https://prove2.me/theorems/30fba9da-57d9-446c-850c-a09b78c13b5d
-- title:
--   Light Reporting Suffix Catalog
-- statement:
--   Definitions and structural lemmas for Light Reporting Suffix Catalog, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixCatalog.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostQueryBounds
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightReportingSuffixCatalog
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix ReportingHostQueryBounds
set_option maxHeartbeats 1800000
variable {lim : Limits}
def stride (V cut : ℕ) : ℕ := (V+1)*downsetCap V cut
def roundBody (pSetup : ℕ) : Stmt :=
  .set 19 (M (v 10 +' v 18)) ;;
  .set 20 (M (v 11 +' v 18)) ;;
  .set 21 (v 14 +' v 18 *' v 15) ;;
  .call pSetup [v 0,v 1,v 2,v 3,v 4,v 19,v 5,v 20,v 6,v 7,v 8,v 9,v 21,v 16,v 17] 22 ;;
  .store (v 13 +' v 18) (v 21)
def body (pSetup : ℕ) : Stmt := .for 18 (v 12) (roundBody pSetup)
def program : Program := LightReportingSuffixSetup.program ++ [body 29]
def time (W V cut offset n : ℕ) : ℕ := n*(LightReportingSuffixSetup.time W V cut offset+200)+30
def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (preL preR : ℕ → Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (cut boxCut stage cL cR baseL baseR inL inR n ptrBase boxBase maskBase work j : ℕ)
    (σ : State) : Prop :=
  ∃ (a b addr r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,cut,boxCut,stage,cL,cR,V,offset,baseL,baseR,inL,inR,n,
      ptrBase,boxBase,stride V boxCut,maskBase,work,j,a,b,addr,r],μ'⟩ ∧
    (∀ i < j, μ' (ptrBase+i) = (boxBase+i*stride V boxCut : ℤ)) ∧
    (∀ i < j, LightBoxStages.StoredThrough μ' (boxBase+i*stride V boxCut) boxCut
      (leafWeight hfit f g stage (preL i) (preR i)) V) ∧
    Kept μ μ' ptrBase
end ThreeSum.LightReportingSuffixCatalog


