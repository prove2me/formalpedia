-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
-- name    : Submission_ThreeSum_LightBlockSourceRetainedStages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:49:57.689995+00:00
-- url     : https://prove2.me/theorems/340bb3ee-809b-4bc2-b4e6-9ed83a94c872
-- title:
--   Light Block Source Retained Stages
-- statement:
--   Definitions and structural lemmas for Light Block Source Retained Stages, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceRetainedStages.lean

import Definitions.Def_Submission_ThreeSum_LightSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
set_option autoImplicit false
namespace ThreeSum.LightBlockSourceRetainedStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000
def histogram (p m : ℕ) (shift : ℤ) (v : ℕ → ℤ) (N r : ℕ) : ℕ :=
  LightHistogram.count (fun j => LightSourceResidues.key p m shift (v j)) r N
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightBlockSourceRetainedStages


