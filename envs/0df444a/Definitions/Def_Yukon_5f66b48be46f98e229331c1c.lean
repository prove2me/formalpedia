-- Prove2me | Definitions.Def_Yukon_5f66b48be46f98e229331c1c
-- name    : Yukon_5f66b48be46f98e229331c1c
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T16:05:11.311019+00:00
-- url     : https://prove2.me/theorems/1e190f52-4e1d-4b58-af59-5c8010e8ce79
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailGates.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailGates.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailGates.lean
--
--   yukon-proof-operation:certificate-split-a2c9e24bfb437b0924f2b3c1f01273ae46e282c93f6144838a31b59fdc11b0a0
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZWY0YWRjMmZmM2M5MTZmYmRjMWIzMzRjODE5MDE2YWQ3MGFjODFjZGI5Nzc4MWY0YzM3ZTI3MmFiYmU4NjI0NyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LWEyYzllMjRiZmI0MzdiMDkyNGYyYjNjMWYwMTI3M2FlNDZlMjgyYzkzZjYxNDQ4MzhhMzFiNTlmZGMxMWIwYTAiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl81ZjY2YjQ4YmU0NmY5OGUyMjkzMzFjMWMiLCJ2IjoyfQ]

import Definitions.Def_Yukon_1c9853f4364428ab76f81792















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailGates
open RCN095 RCN198 RCN263 RCN287 RCN327 LocatorHybridCells
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem z_mixed_bound (f q : FlagDegree) (R capY : ℕ) (hfa : f.all ≤ 31)
    (hfy : f.yz + f.all ≤ 142) (hqa : q.all ≤ R)
    (hqy : q.yz + q.all ≤ capY) :
    flagMixed f q unitZFlag ≤ 31 * capY + 111 * R := by
  have h1 := Nat.mul_le_mul_right q.all hfy
  have h2 := Nat.mul_le_mul_right q.yz hfa
  have h3 := Nat.mul_le_mul_left 31 hqy
  have h4 := Nat.mul_le_mul_left 111 hqa
  simp only [flagMixed, unitZFlag]
  nlinarith

theorem reduced_gate (f : FlagDegree) (t y r : ℕ)
    (hr : 3 ≤ r) (hrcap : r ≤ 31) (hycap : y ≤ 142)
    (hry : r + 2 ≤ y) (hyt : y ≤ t)
    (hfa : f.all ≤ r) (hfy : f.yz + f.all ≤ y) :
    flagMixed f (cellFirstTail t y r) unitZFlag < 2130706433 := by
  have hys : cellB y r + cellS r + 3 = y := by dsimp [cellB,cellS]; omega
  have hs : cellS r + 2 = r := by dsimp [cellS]; omega
  have hqa : (cellFirstTail t y r).all ≤ 7864320 := by
    simp only [cellFirstTail, reducedResidualAgreementFlag, reducedAgreementDirection, cellSupport, RCN198.support, hs, w]
    omega
  have hqy : (cellFirstTail t y r).yz + (cellFirstTail t y r).all ≤ 36962305 := by
    rw [cellFirstTail, reducedResidualAgreementFlag_ys]
    simp only [cellSupport, RCN198.support, hys, w]
    omega
  exact (z_mixed_bound f _ _ _ (hfa.trans hrcap) (hfy.trans hycap) hqa hqy).trans_lt (by decide)

theorem identity_gate (f : FlagDegree) (t y r : ℕ)
    (hr : 3 ≤ r) (hrcap : r ≤ 31) (hycap : y ≤ 142)
    (hry : r + 2 ≤ y) (hyt : y ≤ t)
    (hfa : f.all ≤ r) (hfy : f.yz + f.all ≤ y) :
    flagMixed f (sharpResidualAgreementFlag (cellSupport t y r) w) unitZFlag <
      2130706433 := by
  have hys : cellB y r + cellS r + 3 = y := by dsimp [cellB,cellS]; omega
  have hs : cellS r + 2 = r := by dsimp [cellS]; omega
  have hqa : (sharpResidualAgreementFlag (cellSupport t y r) w).all ≤ 7995331 := by
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection, cellSupport, RCN198.support, hs, w]
    omega
  have hqy : (sharpResidualAgreementFlag (cellSupport t y r) w).yz +
      (sharpResidualAgreementFlag (cellSupport t y r) w).all ≤ 36962023 := by
    rw [sharpResidualAgreementFlag_ys (cellSupport t y r) (by
      simp only [cellSupport, RCN198.support]; omega)]
    simp only [cellSupport, RCN198.support, hys, w]
    omega
  exact (z_mixed_bound f _ _ _ (hfa.trans hrcap) (hfy.trans hycap) hqa hqy).trans_lt (by decide)

end ProximityPrize.SubmissionLower.BoundaryTailGates


