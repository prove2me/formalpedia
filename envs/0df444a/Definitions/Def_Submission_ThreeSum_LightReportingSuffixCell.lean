-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
-- name    : Submission_ThreeSum_LightReportingSuffixCell
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:20:37.079097+00:00
-- url     : https://prove2.me/theorems/c781470e-59a8-42a2-b475-460a2f7ac7e5
-- title:
--   Light Reporting Suffix Cell
-- statement:
--   Definitions and structural lemmas for Light Reporting Suffix Cell, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixCell.lean

import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightReportingSuffixCell
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open LightZetaCell ReportingHostSuffix
variable {lim : Limits} {P : Program}
def body (pLeaf pAddress : ℕ) : Stmt :=
  .set 15 (v 9 *' v 10) ;;
  .call pLeaf [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 8,v 15,v 11,v 12,v 14] 16 ;;
  .call pAddress [v 7,v 8,v 9,v 14] 17 ;;
  .store (v 13 +' v 17) (v 16)
def time (W V : ℕ) : ℕ := LightSignedLeafGeneral.time W+LightDownsetAddress.time V+90
def program : Program := LightSignedLeafCell.program ++ [body 1 5]
def procs : LightSignedLeafCell.Procs program 1 5 where
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
end ThreeSum.LightReportingSuffixCell


