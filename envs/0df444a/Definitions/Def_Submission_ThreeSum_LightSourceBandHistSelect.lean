-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBandHistSelect
-- name    : Submission_ThreeSum_LightSourceBandHistSelect
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:03:00.992066+00:00
-- url     : https://prove2.me/theorems/5867aec0-34e9-43bf-8176-8d8df80f3e74
-- title:
--   Light Source Band Hist Select
-- statement:
--   Definitions and structural lemmas for Light Source Band Hist Select, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandHistSelect.lean

import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSourceBandHistSelect
open Light BandPartition SourceBandPairData SourceBandPairSlices
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000
def finishBody : Stmt := .store (v 2) (v 3) ;; .store (v 2 +' k 1) (v 4)
def rightBody : Stmt :=
  .ite (v 1 <' M (v 0 +' k 3))
    (.set 4 (M (M (v 0 +' k 2) +' k 6 *' v 1 +' k 3))) .skip ;;
  finishBody
def body : Stmt :=
  .set 3 (M (v 0 +' k 4)) ;;
  .set 4 (M (v 0 +' k 4)) ;;
  .ite (v 1 <' M (v 0 +' k 1))
    (.set 3 (M (M (v 0) +' k 6 *' v 1 +' k 3))) .skip ;;
  rightBody
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightSourceBandHistSelect


