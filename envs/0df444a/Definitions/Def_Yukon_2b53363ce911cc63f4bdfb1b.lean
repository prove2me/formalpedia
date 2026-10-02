-- Prove2me | Definitions.Def_Yukon_2b53363ce911cc63f4bdfb1b
-- name    : Yukon_2b53363ce911cc63f4bdfb1b
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T08:11:28.969665+00:00
-- url     : https://prove2.me/theorems/53af71fb-1999-4f78-804e-e3c5716a8084
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailNormalArithmetic.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailNormalArithmetic.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailNormalArithmetic.lean
--
--   yukon-proof-operation:foundation-direct-1d9b591ec7bf3484e3e51510b13b0e6848ca0ee3b9662c2384054a15b104aaf6
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOGVjZmU4ODQzZGZhZDQwNzg0YjBhNDc5ODNiM2JlMmVmMGNiMDYwNGMxYmViMzJiNTUyNjU3ODJlMjZjNDU3MyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTFkOWI1OTFlYzdiZjM0ODRlM2U1MTUxMGIxM2IwZTY4NDhjYTBlZTNiOTY2MmMyMzg0MDU0YTE1YjEwNGFhZjYiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8yYjUzMzYzY2U5MTFjYzYzZjRiZGZiMWIiLCJ2IjoyfQ]

import Definitions.Def_Yukon_1a92fd39ba829710bd7f764c

















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailAlgebra
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
open RCN095 RCN237 RCN206 RCN327 LocatorHybridCells LocatorHybridCellsC1

theorem normalFlag_yz_eq (m v : ℕ) (hv : 1 ≤ v) :
    (m + 3) * v - (m + 1) = (m + 3) * (v - 1) + 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hv
  simp only [Nat.add_sub_cancel_left, Nat.mul_add, Nat.mul_one]
  omega

theorem normalFlag_eq_cell (t y r : ℕ) (hr : 3 ≤ r)
    (hy : r + 2 ≤ y) :
    normalFlag w r (y - r) (t - y) =
      cellHybridCoordinateC1 t y r + w • unitAllFlag := by
  unfold normalFlag cellHybridCoordinateC1 cellRational
  apply congrArg₃ (f := FlagDegree.mk)
  all_goals simp only [normalFlag, cellHybridCoordinateC1, cellRational,
    cellDirection, directionFlag, cellA, cellB, cellS, add_zOnly, add_yz,
    add_all, nsmul_zOnly, nsmul_yz, nsmul_all, unitAllFlag, w]
  all_goals omega

theorem normalFlag_delay_le_smul (w m d r v z : ℕ)
    (hw : 1 ≤ w) (hm : 1 ≤ m) (hd : d ≤ m) (hv : 1 ≤ v) :
    (normalFlag (w - 1 + d) r v z).zOnly ≤ (m • normalFlag w r v z).zOnly ∧
    (normalFlag (w - 1 + d) r v z).yz ≤ (m • normalFlag w r v z).yz ∧
    (normalFlag (w - 1 + d) r v z).all ≤ (m • normalFlag w r v z).all := by
  have hwsub : w - 1 + 1 = w := Nat.sub_add_cancel hw
  have hscale : w - 1 + d + 3 ≤ m * (w + 3) := by nlinarith [Nat.mul_le_mul_right w hm]
  simp only [normalFlag, nsmul_zOnly, nsmul_yz, nsmul_all]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [Nat.mul_le_mul_right z hscale]
  · rw [normalFlag_yz_eq _ _ hv, normalFlag_yz_eq _ _ hv]
    nlinarith [Nat.mul_le_mul_right (v - 1) hscale]
  · nlinarith [Nat.mul_le_mul_right (r - 1) hscale]

theorem low_delay_factor (d m : ℕ) (hd : d ≤ m) (hm : m ≤ 5) :
    w + 1 + d ≤ 2 * 65539 := by
  simp only [w]
  omega

end ProximityPrize.SubmissionLower.BoundaryTailAlgebra


