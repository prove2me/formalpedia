-- Prove2me | Definitions.Def_Yukon_f60f8771f49612b2e4c0149e
-- name    : Yukon_f60f8771f49612b2e4c0149e
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T08:27:12.730905+00:00
-- url     : https://prove2.me/theorems/5162fec3-dd12-4b48-a563-ebdbdc8d9fd1
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeWeightIntervals.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeWeightIntervals.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeWeightIntervals.lean
--
--   yukon-proof-operation:foundation-direct-e419709ed6987d47f5d74e698f01d597c130de4ce16d831d801f0a78b7d2f25f
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYmU0ZWU1YjQxMTA4YTczOTY1YzIyNDQyNGI4MjNhMDkxMjVhNzIzNGNhNzk5NDNjMDYxZTJlNmFmYjVhZWM5MCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWU0MTk3MDllZDY5ODdkNDdmNWQ3NGU2OThmMDFkNTk3YzEzMGRlNGNlMTZkODMxZDgwMWYwYTc4YjdkMmYyNWYiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9mNjBmODc3MWY0OTYxMmIyZTRjMDE0OWUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_2e408f73c84aa0b97341dc8e








































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open RCN100
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Increasing the code cutoff enlarges the coefficient box. This identity
is proved about the original finite sum, not an unverified fast evaluator. -/
theorem coefficientCount_mono_cutoff (w L s : ℕ) :
    Monotone (fun D => coefficientCount D w L s) := by
  intro D1 D2 hD
  unfold coefficientCount
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Nat.mul_le_mul_left
  exact Nat.sub_le_sub_right (Nat.sub_le_sub_right hD _) _

theorem profile_rows_mono_weight {D w L s T R B N alpha beta lo nu : ℕ}
    (hnu : lo ≤ nu)
    (hrows : ∀ mu ≤ B+R, coefficientCount (D-lo) w (L-T) (s-R) +
      N*profileRowRank alpha beta L s T R mu < coefficientCount D w L s) :
    ∀ mu ≤ B+R, coefficientCount (D-nu) w (L-T) (s-R) +
      N*profileRowRank alpha beta L s T R mu < coefficientCount D w L s := by
  intro mu hmu
  have hcoef := coefficientCount_mono_cutoff w (L-T) (s-R)
    (Nat.sub_le_sub_left hnu D)
  exact (Nat.add_le_add_right hcoef _).trans_lt (hrows mu hmu)




end ProximityPrize.SubmissionLower.RelativeBounded6814


