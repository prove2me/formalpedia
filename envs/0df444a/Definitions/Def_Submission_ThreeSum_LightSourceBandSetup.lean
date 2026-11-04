-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
-- name    : Submission_ThreeSum_LightSourceBandSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:02:30.494671+00:00
-- url     : https://prove2.me/theorems/1bfb7d8a-97ea-4296-8e66-299648ea8058
-- title:
--   Light Source Band Setup
-- statement:
--   Definitions and structural lemmas for Light Source Band Setup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandSetup.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBandBatch
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
namespace ThreeSum.LightSourceBandSetup
open Light BandPartition SourceBandLayout
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
def addressBody (pBatch : ℕ) : Stmt :=
  .set 9 (v 6 +' k 6 *' v 8) ;;
  .set 10 (k 3 *' v 4 +' k 1 +' k 2 *' v 7) ;;
  .set 11 (v 9 +' v 8 *' v 10) ;;
  .call pBatch [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11] 12 ;;
  .set 0 (v 11)
def countBody (pDivide pBatch : ℕ) : Stmt :=
  .set 8 (k 0) ;;
  .ite (k 0 <' v 1)
    (.call pDivide [v 1 -' k 1,v 2] 8 ;;
      .set 8 (v 8 +' k 1)) .skip ;;
  addressBody pBatch
def body (pDivide pBatch : ℕ) : Stmt :=
  .set 7 (v 2) ;;
  .ite (v 1 <' v 2) (.set 7 (v 1)) .skip ;;
  countBody pDivide pBatch
def addressTime (n g p m U D : ℕ) : ℕ := LightSourceBandBatch.time n g p m U D+250
def countTime (n g p m U D : ℕ) : ℕ :=
  LightSmallDivide.time (n-1) g+LightSourceBandBatch.time n g p m U D+350
def time (n g p m U D : ℕ) : ℕ :=
  LightSmallDivide.time (n-1) g+LightSourceBandBatch.time n g p m U D+500
structure Procs (P : Program) (pMain : ℕ) where
  pDivide : ℕ
  pBatch : ℕ
  divide : P[pDivide]? = some LightSmallDivide.body
  batch : LightSourceBandBatch.Procs P pBatch
  main : P[pMain]? = some (body pDivide pBatch)
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightSourceBandSetup


