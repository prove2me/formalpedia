-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
-- name    : Submission_ThreeSum_TernaryCoverUniformProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:04:27.040717+00:00
-- url     : https://prove2.me/theorems/b5fe8f85-1651-4d70-b07f-fe539885d45b
-- title:
--   Ternary Cover Uniform Projection
-- statement:
--   Definitions and structural lemmas for Ternary Cover Uniform Projection, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverUniformProjection.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverGenericProjection
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryCoverUniformProjection
open Finset TernaryJointType TernaryCoverLocal TernaryCoverGenericProjection
open TernaryCoverRegularity TernaryCoverOutputCap TernaryCoverProjection TernaryTypeLowerBound
variable {L p : ℕ} [Fact p.Prime]
end ThreeSum.TernaryCoverUniformProjection


