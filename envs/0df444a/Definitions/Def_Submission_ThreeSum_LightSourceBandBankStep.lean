-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBandBankStep
-- name    : Submission_ThreeSum_LightSourceBandBankStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:00:37.828559+00:00
-- url     : https://prove2.me/theorems/1ccacb80-e4a0-4c08-952f-b968c12597a5
-- title:
--   Light Source Band Bank Step
-- statement:
--   Definitions and structural lemmas for Light Source Band Bank Step, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandBankStep.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBandHistSelect
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSourceBandBankStep
open Light GlobalEncoding BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds SubsetAddress LightBlockSourceBatchLayout BlockSourceOccurrenceOrder
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
def body (pSelect pBatch : ℕ) : Stmt :=
  .call pSelect [v 12,v 16,v 13] 17 ;;
  .set 18 (v 0 *' v 1) ;;
  .set 19 (k 5 *' v 14 +' k 2 *' v 18 +' k 2 +' k 2 *' (v 18 +' k 1) *' v 14) ;;
  .set 20 (v 13 +' k 2 *' v 15) ;;
  .set 21 (v 20 +' v 15 *' v 19) ;;
  .set 22 (v 21 +' v 14) ;;
  .set 23 (v 22 +' v 18) ;;
  .set 24 (v 23 +' k 2) ;;
  .call pBatch [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,
    M (v 13),M (v 13 +' k 1),v 13,v 14,v 15,v 20,v 19,v 21,v 22,v 23,v 24] 25
def time (h J cut : ℕ) : ℕ := LightBlockSourceBatch.time (LightBlockSourceCatalog.count h J) h J cut+1500
def word (NL NR h J : ℕ) : ℕ := LightBlockSourceRetainedHost.word NL NR h J+2*NL+2*NR+32
structure Procs (P : Program) (pMain : ℕ) where
  pSelect : ℕ
  pBatch : ℕ
  select : P[pSelect]?=some LightSourceBandHistSelect.body
  batch : LightBlockSourceBatch.Procs P pBatch
  main : P[pMain]?=some (body pSelect pBatch)
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightSourceBandBankStep


