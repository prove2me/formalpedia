-- Prove2me | Definitions.Def_Submission_ThreeSum_LightCoverKeys
-- name    : Submission_ThreeSum_LightCoverKeys
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:26:54.94612+00:00
-- url     : https://prove2.me/theorems/37a077df-dbec-4a25-b877-7f1bddd58b84
-- title:
--   Light Cover Keys
-- statement:
--   Definitions and structural lemmas for Light Cover Keys, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeys.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverRetention
import Definitions.Def_Submission_ThreeSum_LightGlobalKeys
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightCoverKeys
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
def body (pCover pKeys : ℕ) : Stmt :=
  .call pCover [v 0,v 2] 3 ;;
  .call pKeys [M (v 2 +' k 8),M (v 2 +' k 9),M (v 2 +' k 10),
    M (v 2 +' k 6),v 1,M (v 2 +' k 12),M (v 2),v 3] 0
def afterCover (free h : ℕ) : ℕ :=
  LightLocalCoverMetadata.nextFree (LightLocalCoverInit.base free) h
def keyHeader (free h J : ℕ) : ℕ :=
  LightGlobalKeys.scratch (afterCover free h) h+LightRadixKeys.offset (LightGlobalKeys.localCount h) J
def time (h J : ℕ) : ℕ := LightLocalCoverInit.time h+LightGlobalKeys.time h J+200
def space (free h J : ℕ) : ℕ :=
  max (LightLocalCoverInit.space free h) (LightGlobalKeys.space (afterCover free h) h J)
def word (h J : ℕ) : ℕ := max (LightLocalCoverInit.word h) (LightGlobalKeys.word h J)
structure Procs (P : Program) (pMain : ℕ) where
  pCover : ℕ
  pKeys : ℕ
  cover : LightLocalCoverInit.Procs P pCover
  keys : LightGlobalKeys.Procs P pKeys
  main : P[pMain]? = some (body pCover pKeys)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := LightLocalCoverInit.program++
  [LightGlobalKeys.body 54 57 64,LightSubsetEnumerationSetup.body 55 56,powTableBody,
    LightSubsetEnumeration.body 56,LightLocalKeys.body 58 63,LightLocalKeyRow.body 59 60 62,
    fillBody,LightMaskHashes.body 55 61,LightOneHot.body 61,LightArray.linearBody,copyBody,
    LightRadixKeys.body 64 65,LightRadixRows.body 66,LightReportingAffine.body,body 52 53]
def keyProcs : LightGlobalKeys.Procs program 53 :=
  ⟨54,55,56,57,64,65,66,rfl,rfl,rfl,rfl,
    ⟨58,63,rfl,⟨59,60,55,61,62,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl,rfl,rfl⟩
def coverSetupProcs : LightLocalCoverSetup.Procs program 0 :=
  ⟨1,2,3,rfl,rfl,⟨31,8,32,33,34,35,4,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨5,24,29,⟨6,⟨7,12,19,⟨8,9,10,11,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,8,14,15,16,17,18,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨20,11,21,22,23,18,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,
      ⟨18,25,28,rfl,⟨26,21,27,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,⟨30,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩
def coverProcs : LightLocalCoverInit.Procs program 52 :=
  ⟨36,51,0,⟨37,45,50,⟨38,39,40,41,42,43,44,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,
    ⟨46,47,rfl,⟨48,⟨49,rfl,rfl⟩,rfl⟩,rfl⟩,rfl,rfl⟩,
    ⟨1,2,rfl,rfl,rfl⟩,coverSetupProcs,rfl⟩
def programProcs : Procs program 67 := ⟨52,53,coverProcs,keyProcs,rfl⟩
end ThreeSum.LightCoverKeys


