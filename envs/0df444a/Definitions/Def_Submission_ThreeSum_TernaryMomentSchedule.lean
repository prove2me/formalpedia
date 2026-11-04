-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
-- name    : Submission_ThreeSum_TernaryMomentSchedule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:40:29.034218+00:00
-- url     : https://prove2.me/theorems/a24f107b-ebc2-443f-ad7e-9d6694ed80af
-- title:
--   Ternary Moment Schedule
-- statement:
--   Definitions and structural lemmas for Ternary Moment Schedule, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
set_option autoImplicit false
namespace ThreeSum.TernaryMomentSchedule
open Finset TernaryJointType
open scoped BigOperators
def row (k : ℕ) : List (ℕ×ℕ) := (List.range (k+1)).map (fun j => (k,j))
def channels : ℕ→List (ℕ×ℕ)
  | 0 => []
  | t+1 => channels t++row t
def aggregate (xs : List (ℕ×ℕ)) (score : ℕ→ℕ→ℕ→ℤ) (k i : ℕ) : ℤ :=
  (xs.map (fun c => if c.1=k then score c.1 c.2 i else 0)).sum
end ThreeSum.TernaryMomentSchedule


