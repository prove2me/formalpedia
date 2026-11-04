-- Prove2me | Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
-- name    : Submission_ThreeSum_LightMomentZeroDetector
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:39:50.166785+00:00
-- url     : https://prove2.me/theorems/c0468a62-7b56-4b26-a461-29cf748ca10b
-- title:
--   Light Moment Zero Detector
-- statement:
--   Definitions and structural lemmas for Light Moment Zero Detector, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
set_option autoImplicit false
namespace ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector
def atoms (H : ℕ) : ℕ → Expr
  | 0 => v 1
  | offset+1 => if offset≤2*H then M (v 0 +' k offset) else k 0
noncomputable def program (H : ℕ) : Program := [body (atoms H) H]
end ThreeSum.LightMomentZeroDetector


