-- Prove2me | Definitions.Def_Submission_ThreeSum_LightColorScanHost
-- name    : Submission_ThreeSum_LightColorScanHost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:32:24.546577+00:00
-- url     : https://prove2.me/theorems/1b1a94b1-55ce-4ed6-98f0-bdf2b9125efb
-- title:
--   Light Color Scan Host
-- statement:
--   Definitions and structural lemmas for Light Color Scan Host, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorScanHost.lean

import Definitions.Def_Submission_ThreeSum_LightColorScan
import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightColorScanHost
open Light ColorParameters LightColorParametersCosts
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
def body (pScan : ℕ) : Stmt :=
  .set 4 (M (v 2) +' k 1) ;;
  .set 5 (k 81 *' v 4 *' v 4) ;;
  .call pScan [v 0,v 1,v 2,v 3,v 4,v 5] 0
def time (colorTime n : ℕ) : ℕ :=
  LightColorScan.time colorTime (width n) (count (width n))+100
def word (n : ℕ) : ℕ := n+count (width n)+width n+100
structure Procs (P : Program) (pMain : ℕ) where
  pScan : ℕ
  scan : LightColorScan.Procs P pScan
  main : P[pMain]?=some (body pScan)
variable {lim : Limits} {P : Program}
end ThreeSum.LightColorScanHost


