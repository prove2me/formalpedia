-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSparseQuery
-- name    : Submission_ThreeSum_LightSparseQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:22:57.299803+00:00
-- url     : https://prove2.me/theorems/7662fec8-e083-48ac-9ed4-88943f0dee7e
-- title:
--   Light Sparse Query
-- statement:
--   Definitions and structural lemmas for Light Sparse Query, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSparseQuery.lean

import Definitions.Def_Submission_ThreeSum_LightExplicitSum
import Definitions.Def_Submission_ThreeSum_LightCanonicalBoxSum
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSparseQuery
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open scoped BigOperators
variable {lim : Limits} {P : Program}
def queryItems (c t : ℕ) : ℕ := layerOffset c t+c.choose t
def magnitudeBound (W stage c t B D : ℕ) : ℕ :=
  (queryItems c t+1)*(2^W*((2^stage*B)*(2^stage*D)))
def body (pExplicit pBoxes pSign : ℕ) : Stmt :=
  .call pExplicit [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 14,v 15] 16 ;;
  .call pBoxes [v 0,v 12,v 7,v 8,v 9,v 13,v 14,v 15] 17 ;;
  .set 18 (v 16 +' v 17) ;;
  .call pSign [v 18,v 7] 0
def time (W c t : ℕ) : ℕ :=
  LightExplicitSum.time W c t+LightCanonicalBoxSum.time W c t+LightSign.time W+80
def program : Program :=
  [body 1 2 22,LightExplicitSum.body 3 6,LightCanonicalBoxSum.body 3 7,
    LightQueryEnumeration.body 4 5,LightQueryWeights.body 17 20,LightSubsetEnumeration.body 5,
    LightLeafSum.body 8,LightBoxSum.body 9,LightSignedLeaf.body 10 22,
    LightQueryBox.body 11 10,LightStageLookup.body 12 13,LightMaskMinimum.body 17 20,
    LightDownsetSize.body 14 19,LightDownsetAddress.body 14 19,LightSubsetSetup.body 15 17 18,
    buildBody 16 21,fillBody,powTableBody,rankBody 18,LightSubsetOffset.body,
    LightMaskErase.body 20,rowBody 23,LightSign.body,LightArray.linearBody]
def explicitProcs : LightExplicitSum.Procs program 3 6 where
  pWeights := 4
  pPowers := 17
  pErase := 20
  pCore := 5
  pLeaf := 8
  pLookup := 10
  pSign := 22
  pSize := 12
  pAddress := 13
  pSetup := 14
  pBuild := 15
  pFill := 16
  pRow := 21
  pLinear := 23
  pRank := 18
  pOffset := 19
  enumerate := rfl
  weights := rfl
  erase := rfl
  core := rfl
  sum := rfl
  leaf := rfl
  lookup := rfl
  sign := rfl
  size := rfl
  address := rfl
  table := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl
def boxProcs : LightCanonicalBoxSum.Procs program 3 7 where
  pWeights := 4
  pPowers := 17
  pErase := 20
  pCore := 5
  pBox := 9
  pMinimum := 11
  pLookup := 10
  pSize := 12
  pAddress := 13
  pSetup := 14
  pBuild := 15
  pFill := 16
  pRow := 21
  pLinear := 23
  pRank := 18
  pOffset := 19
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
end ThreeSum.LightSparseQuery


