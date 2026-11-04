-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
-- name    : Submission_ThreeSum_LightLocalCoverInit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:19:27.689857+00:00
-- url     : https://prove2.me/theorems/198f16ba-ad4d-48bd-9d6f-a60945addec2
-- title:
--   Light Local Cover Init
-- statement:
--   Definitions and structural lemmas for Light Local Cover Init, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInit.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverMetadata
import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightLocalCoverInit
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
def base (free : ℕ) : ℕ := free+20
def values (free h : ℕ) : List ℤ :=
  LightLocalParameters.values h++LightLocalCoverMetadata.values (base free) h
def body (pParameters pMetadata pSetup : ℕ) : Stmt :=
  .set 2 (v 1 +' k 20) ;;
  .call pParameters [v 0,v 1,v 2] 3 ;;
  .set 4 (M (v 1 +' k 1)) ;;
  .set 5 (M (v 1 +' k 7)) ;;
  .set 6 (v 1 +' k 8) ;;
  .call pMetadata [v 0,v 3,v 4,v 2,v 6] 7 ;;
  .call pSetup [v 0,v 3,v 4,v 5,v 2] 8 ;;
  .set 0 (v 7)
def time (h : ℕ) : ℕ := LightLocalParameters.time h+
  LightLocalCoverMetadata.time h+LightLocalCoverSetup.time h+100
def word (h : ℕ) : ℕ := LightLocalParameters.word h+LightLocalCoverSetup.word h
def space (free h : ℕ) : ℕ :=
  max (LightLocalParameters.space (base free) h) (LightLocalCoverLayout.space (base free) h)
structure Procs (P : Program) (pMain : ℕ) where
  pParameters : ℕ
  pMetadata : ℕ
  pSetup : ℕ
  parameters : LightLocalParameters.Procs P pParameters
  metadata : LightLocalCoverMetadata.Procs P pMetadata
  setup : LightLocalCoverSetup.Procs P pSetup
  main : P[pMain]? = some (body pParameters pMetadata pSetup)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := LightLocalCoverSetup.program++
  [LightLocalParameters.body 37 45 50,LightLocalCounts.body 38,LightSubsetSetup.body 39 43 44,
    LightPascal.buildBody 40 41,fillBody,LightPascal.rowBody 42,LightArray.linearBody,
    powTableBody,LightSubsetAddress.rankBody 44,LightSelectedPrime.body 46 47,sqrtBody,
    LightPrimePool.body 48,LightPrimality.body 49,emodBody,LightSmallDivide.body,
    LightLocalCoverMetadata.body 1 2,body 36 51 0]
def setupProcs : LightLocalCoverSetup.Procs program 0 :=
  ⟨1,2,3,rfl,rfl,⟨31,8,32,33,34,35,4,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨5,24,29,⟨6,⟨7,12,19,⟨8,9,10,11,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,8,14,15,16,17,18,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨20,11,21,22,23,18,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,
      ⟨18,25,28,rfl,⟨26,21,27,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,⟨30,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩
def programProcs : Procs program 52 :=
  ⟨36,51,0,⟨37,45,50,⟨38,39,40,41,42,43,44,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,
    ⟨46,47,rfl,⟨48,⟨49,rfl,rfl⟩,rfl⟩,rfl⟩,rfl,rfl⟩,
    ⟨1,2,rfl,rfl,rfl⟩,setupProcs,rfl⟩
end ThreeSum.LightLocalCoverInit


