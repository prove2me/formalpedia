-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockChildren
-- name    : Submission_ThreeSum_LightBlockChildren
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:54:04.3852+00:00
-- url     : https://prove2.me/theorems/4e4b4267-885b-4435-b0ca-a318e7eaa1f3
-- title:
--   Light Block Children
-- statement:
--   Definitions and structural lemmas for Light Block Children, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildren.lean

import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightBlockChildren
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostMasks
variable {lim : Limits} {P : Program}
def body (pEnum pAffine : ℕ) : Stmt :=
  .call pEnum [v 0,v 2,v 1,v 6,v 9] 10 ;;
  .set 11 (v 4 +' v 2) ;;
  .call pAffine [v 6,v 7,v 10,v 3,k 1] 12 ;;
  .call pAffine [v 6,v 8,v 10,v 11,k 0 -' k 1] 12 ;;
  .set 0 (v 5 -' v 2)
def time (W c h : ℕ) : ℕ :=
  LightQueryEnumeration.time W c h+2*LightReportingAffine.time (c.choose h)+100
def leftMasks {W : ℕ} (A Q : Finset (Fin W)) (h : ℕ) : List ℕ :=
  (missingSets Q h).map fun S => subsetMask (A ∪ S)
def rightMasks {W : ℕ} (B Q : Finset (Fin W)) (h : ℕ) : List ℕ :=
  (missingSets Q h).map fun S => subsetMask (B ∪ (Q \ S))
structure Procs (P : Program) (pEnum pAffine : ℕ) where
  pWeights : ℕ
  pPowers : ℕ
  pErase : ℕ
  pRec : ℕ
  enumBody : P[pEnum]? = some (LightQueryEnumeration.body pWeights pRec)
  weightsBody : P[pWeights]? = some (LightQueryWeights.body pPowers pErase)
  powersBody : P[pPowers]? = some powTableBody
  eraseBody : P[pErase]? = some (LightMaskErase.body pErase)
  recBody : P[pRec]? = some (LightSubsetEnumeration.body pRec)
  affineBody : P[pAffine]? = some LightReportingAffine.body
def program : Program :=
  [body 1 6,LightQueryEnumeration.body 2 5,LightQueryWeights.body 3 4,powTableBody,
    LightMaskErase.body 4,LightSubsetEnumeration.body 5,LightReportingAffine.body]
def procs : Procs program 1 6 := ⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightBlockChildren


