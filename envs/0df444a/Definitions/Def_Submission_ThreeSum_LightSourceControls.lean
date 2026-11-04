-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceControls
-- name    : Submission_ThreeSum_LightSourceControls
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:32:21.844629+00:00
-- url     : https://prove2.me/theorems/fb1946ca-d9fb-4d4a-ae29-46134fc996d1
-- title:
--   Light Source Controls
-- statement:
--   Definitions and structural lemmas for Light Source Controls, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceControls.lean

import Definitions.Def_Submission_ThreeSum_LightSourceControlsSpan
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSourceControls
open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding SubsetAddress
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
def spanWord (h J cut : ℕ) : ℕ :=
  SourceControlLayout.word J (J*(512*h)) (downsetCap (J*(512*h)) cut)
    (LightBlockSourceCatalog.count h J) (Nat.log 2 ((512*h)*localPrime h+1))
    (Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1))
def word (h J cut : ℕ) : ℕ :=
  spanWord h J cut+(J*(512*h)+1)*2^(J*(512*h)+1)+(scheduleSize h+1)^(J+1)+
    2*((512*h)*localPrime h+1)+2*(LightBlockSourceBuild.endpointBound h J+1)+
    modulus h J*localPrime h+J+512*h+localPrime h+cut+scheduleSize h+modulus h J+J*(512*h)+50
def space (work h J : ℕ) : ℕ := work+LightPascal.tableSize (J*(512*h))+(J*(512*h)+1)
def time (h J : ℕ) : ℕ :=
  LightNatPower.time J+LightDownsetSize.time (J*(512*h))+
    log2Time ((512*h)*localPrime h+1)+log2Time (LightBlockSourceBuild.endpointBound h J+1)+2000
def body (pPower pDownset pLog pSpan : ℕ) : Stmt :=
  .call pPower [v 4,v 0] 8 ;;
  .set 9 (v 0 *' v 1) ;;
  .call pDownset [v 9,v 3,v 7] 10 ;;
  .call pLog [v 1 *' v 2 +' k 1] 11 ;;
  .call pLog [v 9 *' (v 5 *' v 2) +' k 1] 12 ;;
  .call pSpan [v 0,v 9,v 10,v 8,v 11,v 12] 13 ;;
  .store (v 6) (v 10) ;;
  .store (v 6 +' k 1) (v 8) ;;
  .store (v 6 +' k 2) (v 13) ;;
  .set 0 (v 13)
structure Procs (P : Program) (pMain : ℕ) where
  pPower : ℕ
  pDownset : ℕ
  pLog : ℕ
  pSpan : ℕ
  pMax : ℕ
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pPowers : ℕ
  pRank : ℕ
  pOffset : ℕ
  power : P[pPower]?=some LightNatPower.body
  downset : P[pDownset]?=some (LightDownsetSize.body pSetup pOffset)
  setup : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]?=some LightSubsetOffset.body
  log : P[pLog]?=some log2Body
  span : P[pSpan]?=some (LightSourceControlsSpan.body pMax)
  maximum : P[pMax]?=some LightSourceControlsMax.body
  main : P[pMain]?=some (body pPower pDownset pLog pSpan)
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightSourceControls


