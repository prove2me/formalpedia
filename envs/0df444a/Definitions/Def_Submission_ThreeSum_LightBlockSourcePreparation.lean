-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockSourcePreparation
-- name    : Submission_ThreeSum_LightBlockSourcePreparation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:53:15.837649+00:00
-- url     : https://prove2.me/theorems/d5100718-cf71-4504-a432-6f8ae2de7737
-- title:
--   Light Block Source Preparation
-- statement:
--   Definitions and structural lemmas for Light Block Source Preparation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourcePreparation.lean

import Definitions.Def_Submission_ThreeSum_LightSourcePreparation
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
set_option autoImplicit false
namespace ThreeSum.LightBlockSourcePreparation
open Light BlockRows BlockIndex BlockEncoding BlockCoefficientRows BlockSourceFlags
open LocalCoverBounds GlobalEncoding
set_option maxHeartbeats 1700000
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightBlockSourcePreparation


