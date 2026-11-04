-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingSuffixQuery
-- name    : Submission_ThreeSum_LightReportingSuffixQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:30:41.707351+00:00
-- url     : https://prove2.me/theorems/462868d4-55a8-4669-8d12-32bdb64e14f9
-- title:
--   Light Reporting Suffix Query
-- statement:
--   Definitions and structural lemmas for Light Reporting Suffix Query, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixQuery.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixExplicit
import Definitions.Def_Submission_ThreeSum_ReportingHostQueryBounds
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingSuffixQuery
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
open scoped BigOperators
variable {lim : Limits}
def body (pExplicit pBoxes pSign : ℕ) : Stmt :=
  .call pExplicit [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 16,v 17] 18 ;;
  .call pBoxes [v 7,v 14,v 9,v 10,v 11,v 15,v 16,v 17] 19 ;;
  .set 20 (v 18 +' v 19) ;;
  .call pSign [v 20,v 9] 0
def program : Program := LightSparseQuery.program ++
  [LightMaskUnion.body 17 20,LightSignedLeafGeneral.body 24 10 22,
    LightReportingSuffixSum.body 25,LightReportingSuffixExplicit.body 3 26,body 27 2 22]
def leafProcs : LightSignedLeafCell.Procs program 25 13 where
  pUnion := 24
  pLookup := 10
  pSign := 22
  pSize := 12
  pSetup := 14
  pBuild := 15
  pFill := 16
  pRow := 21
  pLinear := 23
  pPowers := 17
  pRank := 18
  pOffset := 19
  pErase := 20
  leaf := rfl
  union := rfl
  lookup := rfl
  sign := rfl
  size := rfl
  address := rfl
  setup := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl
  erase := rfl
def explicitProcs : LightReportingSuffixExplicit.Procs program 3 26 :=
  ⟨4,5,25,13,leafProcs,rfl,rfl,rfl,rfl⟩
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
def time (W V c t : ℕ) : ℕ :=
  LightReportingSuffixExplicit.time W c t+LightCanonicalBoxSum.time V c t+LightSign.time V+90
end ThreeSum.LightReportingSuffixQuery


