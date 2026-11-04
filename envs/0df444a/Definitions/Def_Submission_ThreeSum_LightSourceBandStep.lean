-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBandStep
-- name    : Submission_ThreeSum_LightSourceBandStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:56:28.088196+00:00
-- url     : https://prove2.me/theorems/469f5c1a-ac60-4de7-ab50-88f0d2499333
-- title:
--   Light Source Band Step
-- statement:
--   Definitions and structural lemmas for Light Source Band Step, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandStep.lean

import Definitions.Def_Submission_ThreeSum_SourceBandData
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSourceBandStep
open Light BandPartition SourceBandLayout
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
def tailBody (pOriginal : ℕ) : Stmt :=
  .set 15 (v 14 -' v 13) ;;
  .set 16 (v 9 +' v 12 *' v 10) ;;
  .set 17 (v 16 +' v 4) ;;
  .set 18 (v 17 +' v 7) ;;
  .set 19 (v 18 +' v 4 +' k 1) ;;
  .set 20 (v 19 +' v 4) ;;
  .call pOriginal [v 0 +' v 13,v 15,v 3,v 4,v 5,v 16,v 17,v 18,v 19,v 20,v 11] 21 ;;
  .store (v 6 +' k 6 *' v 12) (v 13) ;;
  .store (v 6 +' k 6 *' v 12 +' k 1) (v 15) ;;
  .store (v 6 +' k 6 *' v 12 +' k 2) (v 17) ;;
  .store (v 6 +' k 6 *' v 12 +' k 3) (v 16) ;;
  .store (v 6 +' k 6 *' v 12 +' k 4) (v 18) ;;
  .store (v 6 +' k 6 *' v 12 +' k 5) (v 20)
def body (pOriginal : ℕ) : Stmt :=
  .set 13 (v 12 *' v 2) ;;
  .set 14 ((v 12 +' k 1) *' v 2) ;;
  .ite (v 1 <' v 14) (.set 14 (v 1)) .skip ;;
  tailBody pOriginal
def charge (n g p m U D : ℕ) : ℕ :=
  498*cap n g*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+233*m+333
def tailTime (n g p m U D : ℕ) : ℕ := charge n g p m U D+1000
def time (n g p m U D : ℕ) : ℕ := charge n g p m U D+1200
def word (n g p m U D : ℕ) : ℕ := LightSourceResidues.word p m U D+n+g+2
structure Procs (P : Program) (pMain : ℕ) where
  pOriginal : ℕ
  original : LightSourceBucketOriginal.Procs P pOriginal
  main : P[pMain]? = some (body pOriginal)
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightSourceBandStep


