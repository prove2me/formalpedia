-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockSourceCoverInput
-- name    : Submission_ThreeSum_BlockSourceCoverInput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:59:25.996206+00:00
-- url     : https://prove2.me/theorems/a921c013-0202-4abf-9efc-f69063b15570
-- title:
--   Block Source Cover Input
-- statement:
--   Definitions and structural lemmas for Block Source Cover Input, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCoverInput.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
set_option autoImplicit false
namespace ThreeSum.BlockSourceCoverInput
open Light GlobalEncoding LocalCoverBounds BlockCoefficientRows BlockSourceFlags
structure Input (μ : ℕ → ℤ) (h maps candidates histL histR : ℕ) : Prop where
  candidates : ∀ s : Occurrence h,
    μ (candidates+s.val) = (LightLocalCoverSchedule.candidateAt h s : ℤ)
  leftRows : ∀ s < scheduleSize h, ∀ t < 512*h,
    μ (maps+2*(512*h)*s+t) = (mapRow h false s t : ℤ)
  rightRows : ∀ s < scheduleSize h, ∀ t < 512*h,
    μ (maps+2*(512*h)*s+512*h+t) = (mapRow h true s t : ℤ)
  leftCounts : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
    μ (histL+k*localPrime h+r) = (leftCount h k r : ℤ)
  rightCounts : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
    μ (histR+k*localPrime h+r) = (rightCount h k r : ℤ)
end ThreeSum.BlockSourceCoverInput


