-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverGenericProjection
-- name    : Submission_ThreeSum_TernaryCoverGenericProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:01:41.50635+00:00
-- url     : https://prove2.me/theorems/0c8aa592-2345-4ac3-bab6-ca56208b381f
-- title:
--   Ternary Cover Generic Projection
-- statement:
--   Definitions and structural lemmas for Ternary Cover Generic Projection, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverGenericProjection.lean

import Definitions.Def_Submission_ThreeSum_TernaryProjectionCells
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace ThreeSum.TernaryCoverGenericProjection
open Finset TernaryJointType TernaryCoverLocal
variable {K : Type*} [Field K]
variable {L p : ℕ}
def mixedFiber (α π : DigitType) (a b : ZMod p) (q : Fin L → ZMod p) :
    Finset (LocalEdge L α π) :=
  univ.filter fun e => ∀ i, a*fieldLeft (p := p) e i+b*fieldRight e i = q i
end ThreeSum.TernaryCoverGenericProjection


