-- Prove2me | Definitions.Def_Yukon_32ffc3bd2d664fb5668caa78
-- name    : Yukon_32ffc3bd2d664fb5668caa78
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T07:08:06.053251+00:00
-- url     : https://prove2.me/theorems/0b123778-a61a-408b-b30b-285c3bf8c381
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberSources6814B.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberSources6814B.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberSources6814B.lean
--
--   yukon-proof-operation:foundation-direct-643e4d11aaa036e10b7db1dfd35b6b5828ff944050749b36893779641f7125f1
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNzk2ZjYyNGY2NmJiZjg3YjU3ZmY1NjhhNmIyYTI1OTQ5ZWQwYWI5ZWMzNGJkMDZlNjQ0YmE5ZDc3NzkwNjk4YiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTY0M2U0ZDExYWFhMDM2ZTEwYjdkYjFkZmQzNWI2YjU4MjhmZjk0NDA1MDc0OWIzNjg5Mzc3OTY0MWY3MTI1ZjEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8zMmZmYzNiZDJkNjY0ZmI1NjY4Y2FhNzgiLCJ2IjoyfQ]

import Definitions.Def_Yukon_049050172702f08d24b7329f









































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P6
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 166
def B : ℕ := 73
def s : ℕ := 34
def U : ℕ := 226
def L : ℕ := 3349
def k : ℕ := 8
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      10974806343356610 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 41865508621 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 10974806343356610 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 41865508621 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*41865508621 < 10974806343356610 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap



end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P6

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P7
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 114
def B : ℕ := 47
def s : ℕ := 21
def U : ℕ := 154
def L : ℕ := 3043
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      2066370262589177 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 7882576304 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 2066370262589177 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 7882576304 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*7882576304 < 2066370262589177 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap



end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P7

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P8
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 142
def B : ℕ := 56
def s : ℕ := 26
def U : ℕ := 193
def L : ℕ := 2936
def k : ℕ := 6
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      4390918900144896 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 16750025868 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 4390918900144896 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 16750025868 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*16750025868 < 4390918900144896 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap



end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P8

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P9
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 174
def B : ℕ := 76
def s : ℕ := 36
def U : ℕ := 236
def L : ℕ := 2900
def k : ℕ := 8
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      11277468667084986 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 43020061619 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 11277468667084986 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 43020061619 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*43020061619 < 11277468667084986 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap



end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P9

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P10
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 170
def B : ℕ := 71
def s : ℕ := 32
def U : ℕ := 231
def L : ℕ := 3318
def k : ℕ := 8
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      10949410519932218 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 41768666124 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 10949410519932218 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 41768666124 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*41768666124 < 10949410519932218 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap



end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P10

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P11
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 98
def B : ℕ := 41
def s : ℕ := 19
def U : ℕ := 132
def L : ℕ := 2615
def k : ℕ := 4
def n0 : ℕ := 6

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      1013434585419617 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 3865941597 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 1013434585419617 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 3865941597 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*3865941597 < 1013434585419617 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap



end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P11


