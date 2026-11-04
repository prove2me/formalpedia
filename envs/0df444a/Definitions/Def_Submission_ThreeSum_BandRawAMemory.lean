-- Prove2me | Definitions.Def_Submission_ThreeSum_BandRawAMemory
-- name    : Submission_ThreeSum_BandRawAMemory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:26:51.417446+00:00
-- url     : https://prove2.me/theorems/0f1f64bf-e0e0-4bf1-b10b-becd3e17f616
-- title:
--   Band Raw AMemory
-- statement:
--   Definitions and structural lemmas for Band Raw AMemory, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAMemory.lean

import Definitions.Def_Submission_ThreeSum_LightBandRawARow
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
set_option autoImplicit false
namespace ThreeSum.BandRawA
open Light BandCandidateRows
set_option maxHeartbeats 1400000
structure Stored (μ : ℕ → ℤ) (vals owners positions : ℕ)
    (f : ℕ → ℤ) (ls : List Label) : Prop where
  valueRows : Seg μ vals (values f ls)
  ownerRows : Seg μ owners (ownerLabels ls)
  positionRows : Seg μ positions (positionLabels ls)
end ThreeSum.BandRawA


