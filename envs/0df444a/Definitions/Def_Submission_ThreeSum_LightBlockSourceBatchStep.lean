-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchStep
-- name    : Submission_ThreeSum_LightBlockSourceBatchStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:07:10.597228+00:00
-- url     : https://prove2.me/theorems/b0a58f95-4964-4139-a4f5-f9658fbe2d1b
-- title:
--   Light Block Source Batch Step
-- statement:
--   Definitions and structural lemmas for Light Block Source Batch Step, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBatchStep.lean

import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedHost
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightBlockSourceBatchStep
open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
def body (pSource : ℕ) : Stmt :=
  .set 24 (v 17 +' v 23 *' v 18) ;;
  .set 25 (v 24 +' v 15) ;;
  .set 26 (v 25 +' v 0 *' v 1) ;;
  .set 27 (v 26 +' v 0 *' v 1) ;;
  .set 28 (v 27 +' v 15) ;;
  .set 29 (v 28 +' v 15) ;;
  .set 30 (v 29 +' k 2 *' v 15 +' k 2) ;;
  .set 31 (v 30 +' (v 0 *' v 1 +' k 1) *' v 15) ;;
  .call pSource [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,
    v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31,v 19,v 20,v 21,v 22] 32 ;;
  .store (v 14 +' k 2 *' v 23) (v 30) ;;
  .store (v 14 +' k 2 *' v 23 +' k 1) (v 31)
def time (h J cut : ℕ) : ℕ := LightBlockSourceRetainedHost.time h J cut+500
structure Procs (P : Program) (pMain : ℕ) where
  pSource : ℕ
  source : LightBlockSourceRetainedHost.Procs P pSource
  main : P[pMain]? = some (body pSource)
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightBlockSourceBatchStep


