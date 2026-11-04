-- Prove2me | Definitions.Def_Submission_ThreeSum_LightCanonicalBoxSum
-- name    : Submission_ThreeSum_LightCanonicalBoxSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:19:17.622741+00:00
-- url     : https://prove2.me/theorems/cabcf706-bb4e-463f-866e-f73ac211ddf3
-- title:
--   Light Canonical Box Sum
-- statement:
--   Definitions and structural lemmas for Light Canonical Box Sum, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCanonicalBoxSum.lean

import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightBoxSum
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_ThreeSum_LightBoxStages_program_procs
import Theorems.Thm_ThreeSum_LightBoxSum_program_procs
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_procs
import Theorems.Thm_ThreeSum_LightDownsetSize_program_procs
import Theorems.Thm_ThreeSum_LightQueryBox_program_procs
import Theorems.Thm_ThreeSum_LightStageLookup_program_procs
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs
import Theorems.Thm_ThreeSum_LightZetaCell_program_procs
import Theorems.Thm_ThreeSum_LightZetaPass_program_procs
import Theorems.Thm_ThreeSum_LightZetaStages_program_procs

set_option autoImplicit false
namespace ThreeSum.LightCanonicalBoxSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}
structure Procs (P : Program) (pEnum pSum : ℕ) where
  pWeights : ℕ
  pPowers : ℕ
  pErase : ℕ
  pCore : ℕ
  pBox : ℕ
  pMinimum : ℕ
  pLookup : ℕ
  pSize : ℕ
  pAddress : ℕ
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pRank : ℕ
  pOffset : ℕ
  enumerate : P[pEnum]? = some (LightQueryEnumeration.body pWeights pCore)
  weights : P[pWeights]? = some (LightQueryWeights.body pPowers pErase)
  erase : P[pErase]? = some (LightMaskErase.body pErase)
  core : P[pCore]? = some (LightSubsetEnumeration.body pCore)
  sum : P[pSum]? = some (LightBoxSum.body pBox)
  box : P[pBox]? = some (LightQueryBox.body pMinimum pLookup)
  minimum : P[pMinimum]? = some (LightMaskMinimum.body pPowers pErase)
  lookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress)
  size : P[pSize]? = some (LightDownsetSize.body pSetup pOffset)
  address : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset)
  table : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]? = some LightSubsetOffset.body
def body (pEnum pSum : ℕ) : Stmt :=
  .call pEnum [v 0,v 3,v 4,v 6,v 7] 8 ;;
  .call pSum [v 0,v 1,v 2,v 3,v 4,v 8,v 6,v 5,v 7] 0
def time (W c t : ℕ) : ℕ :=
  LightQueryEnumeration.time W c t+LightBoxSum.time W (c.choose t)+50
def program : Program :=
  [body 1 3,LightQueryEnumeration.body 2 4,LightQueryWeights.body 10 13,
    LightBoxSum.body 5,LightSubsetEnumeration.body 4,LightQueryBox.body 6 7,
    LightMaskMinimum.body 10 13,LightStageLookup.body 8 9,
    LightDownsetSize.body 11 15,LightDownsetAddress.body 11 15,powTableBody,
    LightSubsetSetup.body 12 10 14,buildBody 16 17,LightMaskErase.body 13,
    rankBody 14,LightSubsetOffset.body,fillBody,rowBody 18,LightArray.linearBody]
def program_procs : Procs program 1 3 where
  pWeights := 2
  pPowers := 10
  pErase := 13
  pCore := 4
  pBox := 5
  pMinimum := 6
  pLookup := 7
  pSize := 8
  pAddress := 9
  pSetup := 11
  pBuild := 12
  pFill := 16
  pRow := 17
  pLinear := 18
  pRank := 14
  pOffset := 15
  enumerate := rfl
  weights := rfl
  erase := rfl
  core := rfl
  sum := rfl
  box := rfl
  minimum := rfl
  lookup := rfl
  size := rfl
  address := rfl
  table := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl
end ThreeSum.LightCanonicalBoxSum


