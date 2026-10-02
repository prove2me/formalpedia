-- Prove2me | Definitions.Def_Yukon_c5963d87513e7df48d813483
-- name    : Yukon_c5963d87513e7df48d813483
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T09:55:55.213622+00:00
-- url     : https://prove2.me/theorems/6e93b85b-727e-4329-9cad-88831c11910a
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailGates6808.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailGates6808.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailGates6808.lean
--
--   yukon-proof-operation:foundation-direct-89696b5182bb97c02347545f989532b2882e579c3418110ad31dfac77ac8f47e
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZDBkMjIyZjk0OTJhM2UzYTI3N2M1MjQ3OGY4YWRkMTIzZWYyNWUyYzU2OGFiNDhhYzc3ZWJhNzMzNTk0Zjg3OCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTg5Njk2YjUxODJiYjk3YzAyMzQ3NTQ1Zjk4OTUzMmIyODgyZTU3OWMzNDE4MTEwYWQzMWRmYWM3N2FjOGY0N2UiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9jNTk2M2Q4NzUxM2U3ZGY0OGQ4MTM0ODMiLCJ2IjoyfQ]

import Definitions.Def_Yukon_60a3ec8beeda1bdba065048d














































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailGates6808
open RCN095 RCN198 RCN263 RCN287 RCN327 LocatorHybridCells
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Exact characteristic gates for the actual row, instead of a rectangular cap. -/
def Safe (r y : ℕ) : Prop :=
  r * (cellFirstTail y y r).yz + y * (cellFirstTail y y r).all < 2130706433 ∧
  r * (sharpResidualAgreementFlag (cellSupport y y r) w).yz +
    y * (sharpResidualAgreementFlag (cellSupport y y r) w).all < 2130706433
instance  _root_.ProximityPrize.SubmissionLower.BoundaryTailGates6808.instDecidableSafe (r y : ℕ) : Decidable (Safe r y) := by unfold Safe; infer_instance

theorem z_mixed_bound (f q : FlagDegree) (r y : ℕ)
    (hr : f.all ≤ r) (hy : f.yz + f.all ≤ y) :
    flagMixed f q unitZFlag ≤ r * q.yz + y * q.all := by
  have h1 := Nat.mul_le_mul_right q.yz hr
  have h2 := Nat.mul_le_mul_right q.all hy
  simp only [flagMixed, unitZFlag]
  nlinarith

theorem reduced_gate (f : FlagDegree) (t y r : ℕ)
    (hsafe : Safe r y) (hfa : f.all ≤ r) (hfy : f.yz + f.all ≤ y) :
    flagMixed f (cellFirstTail t y r) unitZFlag < 2130706433 := by
  have hy : (cellFirstTail t y r).yz = (cellFirstTail y y r).yz := rfl
  have hr : (cellFirstTail t y r).all = (cellFirstTail y y r).all := rfl
  exact (z_mixed_bound f _ r y hfa hfy).trans_lt (by rw [hy,hr]; exact hsafe.1)

theorem identity_gate (f : FlagDegree) (t y r : ℕ)
    (hsafe : Safe r y) (hfa : f.all ≤ r) (hfy : f.yz + f.all ≤ y) :
    flagMixed f (sharpResidualAgreementFlag (cellSupport t y r) w) unitZFlag < 2130706433 := by
  have hy : (sharpResidualAgreementFlag (cellSupport t y r) w).yz =
      (sharpResidualAgreementFlag (cellSupport y y r) w).yz := rfl
  have hr : (sharpResidualAgreementFlag (cellSupport t y r) w).all =
      (sharpResidualAgreementFlag (cellSupport y y r) w).all := rfl
  exact (z_mixed_bound f _ r y hfa hfy).trans_lt (by rw [hy,hr]; exact hsafe.2)
end ProximityPrize.SubmissionLower.BoundaryTailGates6808


