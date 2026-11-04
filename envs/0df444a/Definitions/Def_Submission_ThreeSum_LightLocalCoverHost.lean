-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverHost
-- name    : Submission_ThreeSum_LightLocalCoverHost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:00:02.207333+00:00
-- url     : https://prove2.me/theorems/1c5e0d91-8873-404d-8c5c-cb3dc2a68142
-- title:
--   Light Local Cover Host
-- statement:
--   Definitions and structural lemmas for Light Local Cover Host, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverHost.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
import Definitions.Def_Submission_ThreeSum_LightWeightGather
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightLocalCoverHost
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000
def body (pMatrix pGreedy pGather : ℕ) : Stmt :=
  .call pMatrix [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13] 16 ;;
  .set 17 (v 1 *' v 1) ;;
  .call pGreedy [v 12,v 13,v 2,v 17,v 14] 16 ;;
  .set 18 (k 2 *' v 0) ;;
  .call pGather [v 16,v 7,v 15,v 14,v 18] 16 ;;
  .set 0 (v 15)
def time (h : ℕ) : ℕ :=
  LightLocalCoverMatrix.time (512*h) (LocalMaskGraph.vertexCount (512*h) h) (localPrime h) (rows h)+
  LightCoverGreedy.time (rows h) (cols h) (scheduleSize h)+
  LightWeightGather.time (scheduleSize h) (2*(512*h))+200
def word (h : ℕ) : ℕ :=
  LightLocalCoverCandidate.word (512*h) (LocalMaskGraph.vertexCount (512*h) h)
    (localPrime h) (localBucketCap h) (rows h)+
  LightWeightGather.word (rows h) (scheduleSize h) (2*(512*h))
structure Procs (P : Program) (pMain : ℕ) where
  pMatrix : ℕ
  pGreedy : ℕ
  pGather : ℕ
  matrix : LightLocalCoverMatrix.Procs P pMatrix
  greedy : LightCoverGreedy.Procs P pGreedy
  gather : LightWeightGather.Procs P pGather
  main : P[pMain]? = some (body pMatrix pGreedy pGather)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 20 25,LightLocalCoverMatrix.body 2,LightLocalCoverCandidate.body 3 8 15,
    LightWeightDecode.body 4 5,powTableBody,LightWeightRow.body 6,LightRadixDigit.body 7,
    LightSmallDivide.body,LightHashHistogram.body 9 11 13,LightMaskHashes.body 4 10,
    LightOneHot.body 10,LightResidues.residuesBody 12,emodBody,LightHistogram.histogramBody 14,
    fillBody,LightLocalCoverRow.body 16 19,LightPairFlags.body 7 17 18,LightBooleanDot.body,
    LightTrimTest.body,LightSupportMark.body 14,LightCoverGreedy.body 14 21 24,
    LightCoverSelect.body 22 23,LightCoverScores.body 17,LightMinimum.body,LightCoverUpdate.body,
    LightWeightGather.body 26,copyBody]
def programProcs : Procs program 0 :=
  ⟨1,20,25,⟨2,⟨3,8,15,⟨4,5,6,7,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨9,4,10,11,12,13,14,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨16,7,17,18,19,14,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,
    ⟨14,21,24,rfl,⟨22,17,23,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,⟨26,rfl,rfl⟩,rfl⟩
end ThreeSum.LightLocalCoverHost


