-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceBandHostCosts
-- name    : Submission_ThreeSum_SourceBandHostCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:29:02.700627+00:00
-- url     : https://prove2.me/theorems/d6347f02-6c01-4db1-a392-f5c41e62c974
-- title:
--   Source Band Host Costs
-- statement:
--   Definitions and structural lemmas for Source Band Host Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandHostCosts.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBandHostProgram
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
set_option autoImplicit false
namespace ThreeSum.SourceBandHostCosts
open Scales TrimScales StageBounds CostLedger BandScales
end ThreeSum.SourceBandHostCosts


