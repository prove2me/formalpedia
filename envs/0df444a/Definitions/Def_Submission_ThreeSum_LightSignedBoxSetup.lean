-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSignedBoxSetup
-- name    : Submission_ThreeSum_LightSignedBoxSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:03:21.587607+00:00
-- url     : https://prove2.me/theorems/6133e070-7aa6-44a4-9191-1c93fe4e94ba
-- title:
--   Light Signed Box Setup
-- statement:
--   Definitions and structural lemmas for Light Signed Box Setup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedBoxSetup.lean

import Definitions.Def_Submission_ThreeSum_LightSignedLeafTable
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSignedBoxSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def body (pLeafTable pBoxStages : ℕ) : Stmt :=
  .call pLeafTable [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12] 13 ;;
  .call pBoxStages [v 0,v 2,v 10,v 11,v 12] 0
def time (W cut : ℕ) : ℕ := LightSignedLeafTable.time W cut+LightBoxStages.time W cut+60
def program : Program :=
  [body 1 2,LightSignedLeafTable.body 3 4,LightBoxStages.body 9 21,
    LightSubsetEnumerationSetup.body 14 20,LightSignedLeafBatch.body 5,
    LightSignedLeafCell.body 6 10,LightSignedLeafGeneral.body 7 8 19,LightMaskUnion.body 14 18,
    LightStageLookup.body 9 10,LightDownsetSize.body 11 17,LightDownsetAddress.body 11 17,
    LightSubsetSetup.body 12 14 16,buildBody 13 15,fillBody,powTableBody,rowBody 24,
    rankBody 16,LightSubsetOffset.body,LightMaskErase.body 18,LightSign.body,
    LightSubsetEnumeration.body 20,LightZetaPass.body 3 22,LightZetaBatch.body 23,
    LightZetaCell.body 11 17 18 16,LightArray.linearBody]
def procs : LightSignedLeafCell.Procs program 6 10 where
  pUnion := 7
  pLookup := 8
  pSign := 19
  pSize := 9
  pSetup := 11
  pBuild := 12
  pFill := 13
  pRow := 15
  pLinear := 24
  pPowers := 14
  pRank := 16
  pOffset := 17
  pErase := 18
  leaf := rfl
  union := rfl
  lookup := rfl
  sign := rfl
  size := rfl
  address := rfl
  setup := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl
  erase := rfl
end ThreeSum.LightSignedBoxSetup


