-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
-- name    : Submission_ThreeSum_TernaryFrozenQueryStages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:38:52.9319+00:00
-- url     : https://prove2.me/theorems/ec414a2c-e2eb-4a5c-ba37-992d9359368c
-- title:
--   Ternary Frozen Query Stages
-- statement:
--   Definitions and structural lemmas for Ternary Frozen Query Stages, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryStages.lean

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
set_option autoImplicit false
namespace ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
def coords (N K : ℕ) : List (Fin N) := ((List.finRange N).take K).reverse
def stageValue {N : ℕ} (K : ℕ) (H : TritWord N→ℤ) : TritWord N→ℤ :=
  frozenInverse (coords N K) H
end ThreeSum.TernaryFrozenQueryStages


