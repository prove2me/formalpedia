-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
-- name    : Submission_ThreeSum_LightReportingSuffixSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:30:28.280556+00:00
-- url     : https://prove2.me/theorems/2a9e4fba-6d24-4787-9678-2df509bbbe42
-- title:
--   Light Reporting Suffix Setup
-- statement:
--   Definitions and structural lemmas for Light Reporting Suffix Setup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixSetup.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixTable
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingSuffixSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
variable {lim : Limits}
def coreBody (pTable pStages : ℕ) : Stmt :=
  .call pTable [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14] 15 ;;
  .call pStages [v 8,v 2,v 12,v 13,v 14] 0
def body (pPowers pCore : ℕ) : Stmt :=
  .call pPowers [v 14,v 9 +' k 1,k 2] 15 ;;
  .set 16 (M (v 14 +' v 9)) ;;
  .call pCore [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 16,v 10,v 11,v 12,v 13,v 14] 0
def program : Program := LightReportingSuffixTable.program ++ [coreBody 27 2,body 14 28]
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
def coreTime (W V cut : ℕ) : ℕ := LightReportingSuffixTable.time W V cut+LightBoxStages.time V cut+70
def time (W V cut offset : ℕ) : ℕ := powTableTime (offset+1)+coreTime W V cut+100
end ThreeSum.LightReportingSuffixSetup


