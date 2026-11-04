-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
-- name    : Submission_ThreeSum_LightLocalCoverSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:11:18.772574+00:00
-- url     : https://prove2.me/theorems/8ed18cad-68e5-4c30-a61f-5f83786c1040
-- title:
--   Light Local Cover Setup
-- statement:
--   Definitions and structural lemmas for Light Local Cover Setup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverSetup.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightLocalCoverSetup
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 2000000
set_option maxRecDepth 6500
def body (pPower pLog pBuild : ℕ) : Stmt :=
  .set 5 (k 512 *' v 0) ;;
  .set 6 (k 2 *' v 5) ;;
  .call pPower [v 1,v 6] 7 ;;
  .set 8 (v 1 *' v 1) ;;
  .call pLog [v 8] 9 ;;
  .set 10 (k 320 *' (k 2 *' v 0 +' k 1) *' (v 9 +' k 1)) ;;
  .set 11 (v 4 +' v 2) ;;
  .set 12 (v 11 +' v 2 *' v 5) ;;
  .set 13 (v 12 +' v 7 *' v 6) ;;
  .set 14 (v 13 +' k 2 *' v 2) ;;
  .set 15 (v 14 +' k 2 *' v 2) ;;
  .set 16 (v 15 +' v 7 *' v 1) ;;
  .set 17 (v 16 +' v 7 *' v 1) ;;
  .set 18 (v 17 +' v 7 *' v 8) ;;
  .set 19 (v 18 +' v 8 +' v 7 +' v 10) ;;
  .call pBuild [v 5,v 0,v 1,v 7,v 2,v 3,v 4,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 10,v 19] 0
def time (h : ℕ) : ℕ := LightNatPower.time (2*(512*h))+log2Time (cols h)+
  LightLocalCoverBuild.time h+500
def word (h : ℕ) : ℕ := LightLocalCoverBuild.word h+1024+scheduleSize h+rows h+2*cols h+512*h
structure Procs (P : Program) (pMain : ℕ) where
  pPower : ℕ
  pLog : ℕ
  pBuild : ℕ
  power : P[pPower]? = some LightNatPower.body
  log : P[pLog]? = some log2Body
  build : LightLocalCoverBuild.Procs P pBuild
  main : P[pMain]? = some (body pPower pLog pBuild)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 2 3,LightNatPower.body,log2Body,LightLocalCoverBuild.body 31 33 4,
    LightLocalCoverHost.body 5 24 29,LightLocalCoverMatrix.body 6,
    LightLocalCoverCandidate.body 7 12 19,LightWeightDecode.body 8 9,powTableBody,
    LightWeightRow.body 10,LightRadixDigit.body 11,LightSmallDivide.body,
    LightHashHistogram.body 13 15 17,LightMaskHashes.body 8 14,LightOneHot.body 14,
    LightResidues.residuesBody 16,emodBody,LightHistogram.histogramBody 18,fillBody,
    LightLocalCoverRow.body 20 23,LightPairFlags.body 11 21 22,LightBooleanDot.body,
    LightTrimTest.body,LightSupportMark.body 18,LightCoverGreedy.body 18 25 28,
    LightCoverSelect.body 26 27,LightCoverScores.body 21,LightMinimum.body,LightCoverUpdate.body,
    LightWeightGather.body 30,copyBody,LightSubsetEnumerationSetup.body 8 32,
    LightSubsetEnumeration.body 32,LightMaskBitTable.body 34,LightMaskBits.body 8 35,
    LightMaskErase.body 35]
def programProcs : Procs program 0 :=
  ⟨1,2,3,rfl,rfl,⟨31,8,32,33,34,35,4,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨5,24,29,⟨6,⟨7,12,19,⟨8,9,10,11,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,8,14,15,16,17,18,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨20,11,21,22,23,18,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,
      ⟨18,25,28,rfl,⟨26,21,27,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,⟨30,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩
end ThreeSum.LightLocalCoverSetup


