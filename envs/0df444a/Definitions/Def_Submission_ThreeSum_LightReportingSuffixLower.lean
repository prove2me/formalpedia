-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingSuffixLower
-- name    : Submission_ThreeSum_LightReportingSuffixLower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:26:11.160095+00:00
-- url     : https://prove2.me/theorems/aa58abbd-abfc-4c32-8d23-19647967ec9c
-- title:
--   Light Reporting Suffix Lower
-- statement:
--   Definitions and structural lemmas for Light Reporting Suffix Lower, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixLower.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
namespace ThreeSum.LightReportingSuffixLower
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open ReportingHostSuffix MaskErase
variable {lim : Limits} {P : Program}
def scanMask {V : ℕ} (S : Finset (Fin V)) (j : ℕ) : ℕ :=
  subsetMask (S.filter fun i => i.val < j)
def roundBody (pErase : ℕ) : Stmt :=
  .call pErase [v 0,v 2 +' v 7,v 3,v 0,v 4] 8 ;;
  .ite (v 8 =' v 3) .skip (.set 6 (v 6 +' M (v 4 +' v 7)))
def body (pPowers pErase : ℕ) : Stmt :=
  .call pPowers [v 4,v 0 +' k 1,k 2] 5 ;;
  .set 6 (k 0) ;;
  .for 7 (v 1) (roundBody pErase) ;;
  .set 0 (v 6)
def time (W V : ℕ) : ℕ := powTableTime (W+1)+V*(LightMaskErase.time W+100)+100
def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V))
    (μ : ℕ → ℤ) (powers : ℕ) (ret : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ r : ℤ, σ = ⟨frame [W,V,offset,subsetMask (liftSet hfit S),powers,ret,scanMask S j,j,r],μ⟩
def program : Program := [body 1 2,powTableBody,LightMaskErase.body 2]
end ThreeSum.LightReportingSuffixLower


