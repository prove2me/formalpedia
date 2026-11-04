-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryPhysicalMomentBatch
-- name    : Submission_ThreeSum_LightTernaryPhysicalMomentBatch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:49:13.32048+00:00
-- url     : https://prove2.me/theorems/4d0b76a4-f07a-4e36-a42f-5352a5ded9b5
-- title:
--   Light Ternary Physical Moment Batch
-- statement:
--   Definitions and structural lemmas for Light Ternary Physical Moment Batch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPhysicalMomentBatch.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentBatch
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalMomentSupport
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightTernaryPhysicalMomentBatch
open Light TernaryPhysicalMomentSupport FiniteMomentZeroDetector
open scoped BigOperators
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightTernaryPhysicalMomentBatch


