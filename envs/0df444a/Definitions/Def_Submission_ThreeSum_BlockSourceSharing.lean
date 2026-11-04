-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockSourceSharing
-- name    : Submission_ThreeSum_BlockSourceSharing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:35:56.750553+00:00
-- url     : https://prove2.me/theorems/d3be6ba5-4da9-41ca-adae-40f65e2ba493
-- title:
--   Block Source Sharing
-- statement:
--   Definitions and structural lemmas for Block Source Sharing, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_StageBounds
set_option autoImplicit false
namespace ThreeSum.BlockSourceSharing
open BlockEncoding GlobalEncoding BlockIndexedQuery SubsetAddress
open Scales TrimScales CostLedger StageBounds
def sourceCells (n : ℕ) : ℕ :=
  2*bandCount n*scheduleCount n*downsetCap (256*mu n) (mu n)
def zetaWork (n : ℕ) : ℕ :=
  2*bandCount n*scheduleCount n*LightZetaStages.time (256*mu n) (mu n)
def gatherWork (n E : ℕ) : ℕ :=
  2*bandCount n*scheduleCount n*LightSourceGather.time (downsetCap (256*mu n) (mu n)) E
end ThreeSum.BlockSourceSharing


