-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
-- name    : Submission_ThreeSum_SourceBandPairCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:11:53.940623+00:00
-- url     : https://prove2.me/theorems/ac42a323-fc2d-4d9d-bfe5-2abc104d66b3
-- title:
--   Source Band Pair Costs
-- statement:
--   Definitions and structural lemmas for Source Band Pair Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairCosts.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBandPair
set_option autoImplicit false
namespace ThreeSum.SourceBandPairCosts
open Scales TrimScales StageBounds CostLedger BandScales SourceBandPairData
end ThreeSum.SourceBandPairCosts


