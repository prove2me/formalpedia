-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSignedLeafCell
-- name    : Submission_ThreeSum_LightSignedLeafCell
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:54:07.688882+00:00
-- url     : https://prove2.me/theorems/4615983c-c449-44e2-b204-13520299b385
-- title:
--   Light Signed Leaf Cell
-- statement:
--   Definitions and structural lemmas for Light Signed Leaf Cell, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafCell.lean

import Definitions.Def_Submission_ThreeSum_LightSignedLeafGeneral
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSignedLeafCell
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open LightZetaCell
variable {lim : Limits} {P : Program}
structure Procs (P : Program) (pLeaf pAddress : ℕ) where
  (pUnion pLookup pSign pSize pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ)
  leaf : P[pLeaf]? = some (LightSignedLeafGeneral.body pUnion pLookup pSign)
  union : P[pUnion]? = some (LightMaskUnion.body pPowers pErase)
  lookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress)
  sign : P[pSign]? = some LightSign.body
  size : P[pSize]? = some (LightDownsetSize.body pSetup pOffset)
  address : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset)
  setup : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]? = some LightSubsetOffset.body
  erase : P[pErase]? = some (LightMaskErase.body pErase)
def body (pLeaf pAddress : ℕ) : Stmt :=
  .call pLeaf [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 12] 13 ;;
  .call pAddress [v 0,v 7,v 8,v 12] 14 ;;
  .store (v 11 +' v 14) (v 13)
def time (W : ℕ) : ℕ := LightSignedLeafGeneral.time W+LightDownsetAddress.time W+70
def program : Program :=
  [body 1 5,LightSignedLeafGeneral.body 2 3 15,LightMaskUnion.body 11 14,
    LightStageLookup.body 4 5,LightDownsetSize.body 6 13,LightDownsetAddress.body 6 13,
    LightSubsetSetup.body 7 11 12,buildBody 8 9,fillBody,rowBody 10,
    LightArray.linearBody,powTableBody,rankBody 12,LightSubsetOffset.body,
    LightMaskErase.body 14,LightSign.body]
def procs : Procs program 1 5 where
  pUnion := 2
  pLookup := 3
  pSign := 15
  pSize := 4
  pSetup := 6
  pBuild := 7
  pFill := 8
  pRow := 9
  pLinear := 10
  pPowers := 11
  pRank := 12
  pOffset := 13
  pErase := 14
  leaf := rfl
  union := rfl
  lookup := rfl
  sign := rfl
  size := rfl
  address := rfl
  setup := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl
  erase := rfl
end ThreeSum.LightSignedLeafCell


