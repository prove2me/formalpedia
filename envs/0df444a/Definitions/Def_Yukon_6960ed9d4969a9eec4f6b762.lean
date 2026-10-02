-- Prove2me | Definitions.Def_Yukon_6960ed9d4969a9eec4f6b762
-- name    : Yukon_6960ed9d4969a9eec4f6b762
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T09:28:29.298656+00:00
-- url     : https://prove2.me/theorems/3d21004e-b5db-447e-9da4-1e90a9b2738b
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeGeneralRank6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeGeneralRank6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeGeneralRank6814.lean
--
--   yukon-proof-operation:foundation-direct-9dca5c5e2988461b9d39acb4c7e8a842cfd8d9af1dbc78da552470a371e43f2c
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiM2E5MTg0NTM2ZTVmMzg5MjhjZTI0OTU5ZmQzMDAzZjUyMjU0NDMxY2IyNWExZjAxZjFkODdkYmUyZGY5MTQ2NiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTlkY2E1YzVlMjk4ODQ2MWI5ZDM5YWNiNGM3ZThhODQyY2ZkOGQ5YWYxZGJjNzhkYTU1MjQ3MGEzNzFlNDNmMmMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl82OTYwZWQ5ZDQ5NjlhOWVlYzRmNmI3NjIiLCJ2IjoyfQ]

import Definitions.Def_Yukon_25bf5197adc4dcc71dc488df









































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The existing rank polynomial with the correct truncated removal
range min(s,m/2). This also covers the eleven saved profile instances
outside the old 2*s<=m simplification. -/
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open scoped BigOperators
open LocatorFastKernelArithmetic ClosedRank
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

theorem rankRow_twice_general (m L s r : ℕ) (hr : r<m) (hshape : m+s≤L+1) :
    2*(rankRow m L s r : ℤ)=
      (r+1 : ℤ)*(s+1)*(2*L+2-r-s)-
        if r<m-min s (m/2) then 0 else
          (2*r+1-m : ℤ)*(s+1-m+r)*(2*L+2-r-s) := by
  let h := min (r+1) (m-r)
  have hl : r+s≤L := by omega
  have hle := rectangularCount_shift_le (r+1) (s+1) h L (by omega)
  have hsource := rectangularCount_twice (r+1) (s+1) 0 L (by omega)
  have hsource' : 2*(rectangularCount (r+1) (s+1) 0 L : ℤ)=
      (r+1 : ℤ)*(s+1)*(2*L+2-r-s) := by
    push_cast at hsource
    nlinarith only [hsource]
  unfold rankRow
  change 2*((rectangularCount (r+1) (s+1) 0 L-
    rectangularCount (r+1-h) (s+1-h) h L : ℕ) : ℤ)=_
  rw [Nat.cast_sub hle,mul_sub,hsource']
  by_cases hearly : r<m-min s (m/2)
  · rw [if_pos hearly]
    have hzero : r+1-h=0 ∨ s+1-h=0 := by dsimp [h]; omega
    rcases hzero with hh | hh <;> simp [hh,rectangularCount]
  · rw [if_neg hearly]
    have heqh : h=m-r := by dsimp [h]; omega
    have hhr : h≤r+1 := by dsimp [h]; omega
    have hhs : h≤s+1 := by omega
    have hkernel := rectangularCount_twice (r+1-h) (s+1-h) h L (by omega)
    simp only [Nat.cast_sub hhr,Nat.cast_sub hhs,Nat.cast_add,Nat.cast_one] at hkernel
    have hhcast : (h : ℤ)=m-r := by rw [heqh,Nat.cast_sub (by omega : r≤m)]
    rw [hhcast] at hkernel
    nlinarith only [hkernel]

theorem sum_removed_rows_general (m L s k : ℕ) (hk : k≤m) :
    (∑ r∈Finset.range m, if r<m-k then (0 : ℤ) else removedTwice m L s ((m : ℤ)-r))=
      ∑ j∈Finset.range k, removedTwice m L s (j+1) := by
  let f : ℕ → ℤ := fun r => if r<m-k then 0 else removedTwice m L s ((m : ℤ)-r)
  change (∑ r∈Finset.range m, f r)=_
  have hsplit := Finset.sum_range_add f (m-k) k
  rw [Nat.sub_add_cancel hk] at hsplit
  rw [hsplit]
  have hz : (∑ r∈Finset.range (m-k), f r)=0 := by
    apply Finset.sum_eq_zero
    intro r hr
    simp [f,Finset.mem_range.mp hr]
  rw [hz,zero_add]
  calc
    _=∑ j∈Finset.range k, f (m-k+(k-1-j)) :=
      (Finset.sum_range_reflect (fun r => f (m-k+r)) k).symm
    _=_ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hlate : ¬m-k+(k-1-j)<m-k := by omega
      have hindex : (m : ℤ)-(m-k+(k-1-j) : ℕ)=(j : ℤ)+1 := by
        have he : m-k+(k-1-j)+j+1=m := by omega
        have hi : ((m-k+(k-1-j) : ℕ) : ℤ)+j+1=m := by exact_mod_cast he
        omega
      simp only [f,if_neg hlate,hindex]

def rankTwelve (m L s : ℕ) : ℤ :=
  sourceTwelve m L s-removedPartialTwelve m L s (min s (m/2) : ℕ)

theorem localRankBound_twelve (m L s : ℕ) (hshape : m+s≤L+1) :
    12*(RCN119.localRankBound m L s : ℤ)=rankTwelve m L s := by
  rw [localRankBound_eq_fastLocalRankBound m L s hshape]
  have hfast : fastLocalRankBound m L s=∑ r∈Finset.range m, rankRow m L s r := by
    unfold fastLocalRankBound
    rw [LocatorLowQuotient.kernelSumRange_eq]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have he : min r L=r := min_eq_left (by omega)
    simp only [he,rankRow]
  have hrow (r : ℕ) (hr : r∈Finset.range m) :
      2*(rankRow m L s r : ℤ)=sourceTwice L s r-
        (if r<m-min s (m/2) then 0 else removedTwice m L s ((m : ℤ)-r)) := by
    rw [rankRow_twice_general m L s r (Finset.mem_range.mp hr) hshape]
    split_ifs <;> simp only [sourceTwice,removedTwice] <;> ring
  have hsum : 2*(fastLocalRankBound m L s : ℤ)=
      (∑ r∈Finset.range m, sourceTwice L s r)-
        ∑ j∈Finset.range (min s (m/2)), removedTwice m L s (j+1) := by
    rw [hfast,Nat.cast_sum,Finset.mul_sum]
    rw [Finset.sum_congr rfl hrow,Finset.sum_sub_distrib,
      sum_removed_rows_general m L s (min s (m/2)) (by omega)]
  have hh := congrArg (fun z : ℤ => 6*z) hsum
  rw [mul_sub,sum_sourceTwice,sum_removedTwice] at hh
  unfold rankTwelve
  nlinarith only [hh]



end ProximityPrize.SubmissionLower.RelativeCertificate6814


