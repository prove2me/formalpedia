-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceBandCosts
-- name    : Submission_ThreeSum_SourceBandCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:56:26.053065+00:00
-- url     : https://prove2.me/theorems/b485db0b-972a-4f41-986f-b3834382684a
-- title:
--   Source Band Costs
-- statement:
--   Definitions and structural lemmas for Source Band Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandCosts.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
set_option autoImplicit false
namespace ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds
end ThreeSum.SourceBandCosts


