-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverBuild
-- name    : Submission_ThreeSum_LightLocalCoverBuild
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:04:09.665207+00:00
-- url     : https://prove2.me/theorems/962ea66b-1706-48f5-a702-024ca1aad82d
-- title:
--   Light Local Cover Build
-- statement:
--   Definitions and structural lemmas for Light Local Cover Build, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverBuild.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverHost
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightMaskBitTable
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightLocalCoverBuild
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
set_option maxHeartbeats 1500000
set_option maxRecDepth 6000
def body (pEnum pBits pHost : ℕ) : Stmt :=
  .call pEnum [v 0,v 1,v 6,v 14] 17 ;;
  .call pBits [v 0,v 6,v 7,v 4,v 14] 17 ;;
  .call pHost [v 0,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16] 0
def time (h : ℕ) : ℕ := LightSubsetEnumerationSetup.time (512*h) h+
  LightMaskBitTable.time (512*h) (LocalMaskGraph.vertexCount (512*h) h)+
  LightLocalCoverHost.time h+200
def word (h : ℕ) : ℕ := LightLocalCoverHost.word h+2^(512*h+1)
structure Procs (P : Program) (pMain : ℕ) where
  pEnum : ℕ
  pPowers : ℕ
  pEnumRec : ℕ
  pBits : ℕ
  pOneBits : ℕ
  pErase : ℕ
  pHost : ℕ
  enum : P[pEnum]? = some (LightSubsetEnumerationSetup.body pPowers pEnumRec)
  powers : P[pPowers]? = some powTableBody
  enumRec : P[pEnumRec]? = some (LightSubsetEnumeration.body pEnumRec)
  bits : P[pBits]? = some (LightMaskBitTable.body pOneBits)
  oneBits : P[pOneBits]? = some (LightMaskBits.body pPowers pErase)
  erase : P[pErase]? = some (LightMaskErase.body pErase)
  host : LightLocalCoverHost.Procs P pHost
  main : P[pMain]? = some (body pEnum pBits pHost)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 28 30 1,LightLocalCoverHost.body 2 21 26,LightLocalCoverMatrix.body 3,
    LightLocalCoverCandidate.body 4 9 16,LightWeightDecode.body 5 6,powTableBody,
    LightWeightRow.body 7,LightRadixDigit.body 8,LightSmallDivide.body,
    LightHashHistogram.body 10 12 14,LightMaskHashes.body 5 11,LightOneHot.body 11,
    LightResidues.residuesBody 13,emodBody,LightHistogram.histogramBody 15,fillBody,
    LightLocalCoverRow.body 17 20,LightPairFlags.body 8 18 19,LightBooleanDot.body,
    LightTrimTest.body,LightSupportMark.body 15,LightCoverGreedy.body 15 22 25,
    LightCoverSelect.body 23 24,LightCoverScores.body 18,LightMinimum.body,LightCoverUpdate.body,
    LightWeightGather.body 27,copyBody,LightSubsetEnumerationSetup.body 5 29,
    LightSubsetEnumeration.body 29,LightMaskBitTable.body 31,LightMaskBits.body 5 32,
    LightMaskErase.body 32]
def programProcs : Procs program 0 :=
  ⟨28,5,29,30,31,32,1,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨2,21,26,⟨3,⟨4,9,16,⟨5,6,7,8,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨10,5,11,12,13,14,15,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨17,8,18,19,20,15,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,
      ⟨15,22,25,rfl,⟨23,18,24,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,⟨27,rfl,rfl⟩,rfl⟩,rfl⟩
end ThreeSum.LightLocalCoverBuild


