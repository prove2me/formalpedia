-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverMetadata
-- name    : Submission_ThreeSum_LightLocalCoverMetadata
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:15:19.764576+00:00
-- url     : https://prove2.me/theorems/77ba28df-4e05-405a-996a-06e8e5c8e874
-- title:
--   Light Local Cover Metadata
-- statement:
--   Definitions and structural lemmas for Light Local Cover Metadata, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverMetadata.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightLocalCoverMetadata
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
open LightLocalCoverSetup (word)
set_option maxHeartbeats 2000000
set_option maxRecDepth 8500
def nextFree (base h : ℕ) : ℕ := scheduleMaps base h+scheduleSize h*(2*(512*h))
def values (base h : ℕ) : List ℤ :=
  [512*h,2*h,scheduleSize h,rows h,scheduleMaps base h,candidates base h,
    hist0 base h,hist1 base h,maps base h,matrixPtr base h,nextFree base h,cols h]
def body (pPower pLog : ℕ) : Stmt :=
  .set 5 (k 512 *' v 0) ;;
  .set 6 (k 2 *' v 5) ;;
  .call pPower [v 1,v 6] 7 ;;
  .set 8 (v 1 *' v 1) ;;
  .call pLog [v 8] 9 ;;
  .set 10 (k 320 *' (k 2 *' v 0 +' k 1) *' (v 9 +' k 1)) ;;
  .set 11 (v 3 +' v 2) ;;
  .set 12 (v 11 +' v 2 *' v 5) ;;
  .set 13 (v 12 +' v 7 *' v 6) ;;
  .set 14 (v 13 +' k 2 *' v 2) ;;
  .set 15 (v 14 +' k 2 *' v 2) ;;
  .set 16 (v 15 +' v 7 *' v 1) ;;
  .set 17 (v 16 +' v 7 *' v 1) ;;
  .set 18 (v 17 +' v 7 *' v 8) ;;
  .set 19 (v 18 +' v 8 +' v 7 +' v 10) ;;
  .set 20 (v 18 +' v 8 +' v 7) ;;
  .set 21 (v 19 +' v 10 *' v 6) ;;
  .set 22 (k 2 *' v 0) ;;
  .store (v 4) (v 5) ;;
  .store (v 4 +' k 1) (v 22) ;;
  .store (v 4 +' k 2) (v 10) ;;
  .store (v 4 +' k 3) (v 7) ;;
  .store (v 4 +' k 4) (v 19) ;;
  .store (v 4 +' k 5) (v 20) ;;
  .store (v 4 +' k 6) (v 15) ;;
  .store (v 4 +' k 7) (v 16) ;;
  .store (v 4 +' k 8) (v 12) ;;
  .store (v 4 +' k 9) (v 17) ;;
  .store (v 4 +' k 10) (v 21) ;;
  .store (v 4 +' k 11) (v 8) ;;
  .set 0 (v 21)
def time (h : ℕ) : ℕ := LightNatPower.time (2*(512*h))+log2Time (cols h)+1000
structure Procs (P : Program) (pMain : ℕ) where
  pPower : ℕ
  pLog : ℕ
  power : P[pPower]? = some LightNatPower.body
  log : P[pLog]? = some log2Body
  main : P[pMain]? = some (body pPower pLog)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1 2,LightNatPower.body,log2Body]
def programProcs : Procs program 0 := ⟨1,2,rfl,rfl,rfl⟩
end ThreeSum.LightLocalCoverMetadata


