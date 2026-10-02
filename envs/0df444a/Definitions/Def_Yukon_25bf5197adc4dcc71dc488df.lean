-- Prove2me | Definitions.Def_Yukon_25bf5197adc4dcc71dc488df
-- name    : Yukon_25bf5197adc4dcc71dc488df
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T09:10:35.576985+00:00
-- url     : https://prove2.me/theorems/2f0951ae-738c-4568-99b1-e1e423b90ad3
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeCountMonotone6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCountMonotone6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCountMonotone6814.lean
--
--   yukon-proof-operation:foundation-direct-9af82b6f6b059a09ebf899b403498446a77420c6d096317fb272546c5ee89a96
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMDE4YTUzZjYxMThjMDE5OTc3ZmYzYWNiMzY5MGZlNWFlNDg5NTdiMzU3MzVmODUzYjVlNTZkMGI1MjMxZmRiNyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTlhZjgyYjZmNmIwNTlhMDllYmY4OTliNDAzNDk4NDQ2YTc3NDIwYzZkMDk2MzE3ZmIyNzI1NDZjNWVlODlhOTYiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8yNWJmNTE5N2FkYzRkY2M3MWRjNDg4ZGYiLCJ2IjoyfQ]

import Definitions.Def_Yukon_20e9cbe0f908e5fcbffc0920








































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open scoped BigOperators
open RCN100
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem coefficientCount_mono_caps (D w : ℕ) {L L' s s' : ℕ}
    (hL : L≤L') (hs : s≤s') : coefficientCount D w L s≤coefficientCount D w L' s' := by
  unfold coefficientCount
  calc
    _≤∑ i∈Finset.range (L+1), ∑ j∈Finset.range (s+1),
        (L'+1-i-j)*(D-w*i-(w-1)*j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact Nat.mul_le_mul_right _ (by omega)
    _≤∑ i∈Finset.range (L+1), ∑ j∈Finset.range (s'+1),
        (L'+1-i-j)*(D-w*i-(w-1)*j) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)
    _≤_ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)

theorem coefficientCount_strictMono_cutoff (w L s : ℕ) :
    StrictMono (fun D => coefficientCount D w L s) := by
  intro D D' hD
  unfold coefficientCount
  apply Finset.sum_lt_sum
  · intro i _
    apply Finset.sum_le_sum
    intro j _
    exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.sub_le_sub_right hD.le _) _)
  · refine ⟨0,by simp,?_⟩
    apply Finset.sum_lt_sum
    · intro j _
      exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.sub_le_sub_right hD.le _) _)
    · refine ⟨0,by simp,?_⟩
      simpa using Nat.mul_lt_mul_of_pos_left hD (by omega : 0<L+1)

theorem multiple_count_lt_source (D w L s nu T R : ℕ) (hD : 0<D) (hnu : 0<nu) :
    coefficientCount (D-nu) w (L-T) (s-R)<coefficientCount D w L s :=
  (coefficientCount_mono_caps (D-nu) w (Nat.sub_le _ _) (Nat.sub_le _ _)).trans_lt
    (coefficientCount_strictMono_cutoff w L s (by omega))

theorem row_test_of_rearranged (source multiple outer inner n : ℕ)
    (hbase : multiple<source) (h : multiple+n*outer<source+n*inner) :
    multiple+n*(outer-inner)<source := by
  by_cases hio : inner≤outer
  · have he := congrArg (fun v : ℕ => n*v) (Nat.sub_add_cancel hio)
    rw [Nat.mul_add] at he
    omega
  · rw [Nat.sub_eq_zero_of_le (by omega : outer ≤ inner),mul_zero,add_zero]
    exact hbase





end ProximityPrize.SubmissionLower.RelativeCertificate6814


