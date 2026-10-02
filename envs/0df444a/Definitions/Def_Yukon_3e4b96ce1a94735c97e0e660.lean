-- Prove2me | Definitions.Def_Yukon_3e4b96ce1a94735c97e0e660
-- name    : Yukon_3e4b96ce1a94735c97e0e660
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:26:03.983807+00:00
-- url     : https://prove2.me/theorems/6bb5f39f-871d-4a6b-bff8-59dae4798d4c
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailArithmetic.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailArithmetic.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailArithmetic.lean
--
--   yukon-proof-operation:foundation-direct-06060da032598aaccc164c9409a99a4a541e88e3d54826e540df054a12557188
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTY0NzhlOGZhMjgyNmM5NjNiNTkzZjI2MTk5NjNmZDY5MzNjOWVlYTQ2MGExYTcxZmIzZmFjMTM0OWFhMTQ3NCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTA2MDYwZGEwMzI1OThhYWNjYzE2NGM5NDA5YTk5YTRhNTQxZTg4ZTNkNTQ4MjZlNTQwZGYwNTRhMTI1NTcxODgiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8zZTRiOTZjZTFhOTQ3MzVjOTdlMGU2NjAiLCJ2IjoyfQ]

import Definitions.Def_Yukon_ca285380b3940c88ff602179







































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTail

theorem weighted_tail_bound {n j a b c : ℤ}
    (hn : 2 ≤ n) (hj0 : 0 ≤ j) (hjn : j ≤ n - 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a - b ≤ 2 * c) :
    2 * (j * a + (n - 1 - j) * b + max (n - 2 - 2 * j) 0 * c) ≥
      2 * (n - 1) * a - n * max (a - b) 0 := by
  by_cases hpos : 0 ≤ n - 2 - 2 * j
  · rw [max_eq_left hpos]
    by_cases hd : 0 ≤ a - b
    · rw [max_eq_left hd]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hd)]
      nlinarith
  · rw [max_eq_right (le_of_not_ge hpos)]
    by_cases hd : 0 ≤ a - b
    · rw [max_eq_left hd]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hd)]
      nlinarith

theorem leading_separation {n j a b c : ℤ}
    (hn : 2 ≤ n) (hj0 : 1 ≤ j) (hjn : j ≤ n - 1)
    (hc : 0 ≤ c) (hgap : 2 * c < a - b) :
    j * a + (n - 1 - j) * b + max (n - 2 - 2 * j) 0 * c >
      (n - 1) * b + (n - 2) * c := by
  by_cases hpos : 0 ≤ n - 2 - 2 * j
  · rw [max_eq_left hpos]
    nlinarith
  · rw [max_eq_right (le_of_not_ge hpos)]
    nlinarith

theorem max_shift_identity {u v p : ℤ}
    (hv : 0 ≤ v) (hvu : v ≤ u) :
    max (max (2 * u) (v + max p 0) - 2 * u) 0 =
      max (p - (2 * u - v)) 0 := by
  simp [max_def]
  omega

end ProximityPrize.SubmissionLower.BoundaryTail


