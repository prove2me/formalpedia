-- Prove2me | Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
-- name    : Submission_ThreeSum_LightOriginalSurvivors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:40:43.853699+00:00
-- url     : https://prove2.me/theorems/e959e4c4-4ba8-448e-892e-02659f72aeaa
-- title:
--   Light Original Survivors
-- statement:
--   Definitions and structural lemmas for Light Original Survivors, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivors.lean

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable
def indices (keys : ℕ → ℕ) (n : ℕ) : List ℕ := good keys (counts keys n) n
def index (keys : ℕ → ℕ) (n j : ℕ) : ℕ :=
  if hj : j < (indices keys n).length then (indices keys n)[j] else 0
end ThreeSum.LightOriginalSurvivors


