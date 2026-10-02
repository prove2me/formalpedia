-- Prove2me | Definitions.Def_Yukon_8f48e19d97a036eba8efa3e4
-- name    : Yukon_8f48e19d97a036eba8efa3e4
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T08:01:12.088974+00:00
-- url     : https://prove2.me/theorems/b7fec61b-14e5-4c19-9eba-2637e5553dbd
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberSources6814E.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberSources6814E.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberSources6814E.lean
--
--   yukon-proof-operation:foundation-direct-c4cf5c3a21b2a51b75228e9bc9aa000d50b254844abbd66d6aa2b60da8f21995
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMzA2NmE0NDk5MzdkZDA0NDI2ZDljZGU3NmI5NmUxYTBjZmVkY2IwOTBlNTY1NTUxMmRjOTAyYjdkY2I2NTM2MiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWM0Y2Y1YzNhMjFiMmE1MWI3NTIyOGU5YmM5YWEwMDBkNTBiMjU0ODQ0YWJiZDY2ZDZhYTJiNjBkYThmMjE5OTUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl84ZjQ4ZTE5ZDk3YTAzNmViYThlZmEzZTQiLCJ2IjoyfQ]

import Definitions.Def_Yukon_dc1f37daf166378f215b7cc0









































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P24
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 190
def B : ℕ := 84
def s : ℕ := 40
def U : ℕ := 258
def L : ℕ := 3236
def k : ℕ := 9
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      18159987378448347 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 69274849016 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 18159987378448347 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 69274849016 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*69274849016 < 18159987378448347 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap



end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P24

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P25
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 111
def B : ℕ := 46
def s : ℕ := 21
def U : ℕ := 151
def L : ℕ := 3411
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      2116605519616735 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 8074209199 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 2116605519616735 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 8074209199 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*8074209199 < 2116605519616735 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap



end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P25

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P26
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 189
def B : ℕ := 83
def s : ℕ := 39
def U : ℕ := 257
def L : ℕ := 3277
def k : ℕ := 9
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      17809304291613422 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 67937077781 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 17809304291613422 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 67937077781 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*67937077781 < 17809304291613422 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap



end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P26

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P27
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 72
def B : ℕ := 31
def s : ℕ := 14
def U : ℕ := 98
def L : ℕ := 995
def k : ℕ := 2
def n0 : ℕ := 3

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      119658696302766 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 456461313 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 119658696302766 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 456461313 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*456461313 < 119658696302766 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap



end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P27

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P28
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 104
def B : ℕ := 45
def s : ℕ := 21
def U : ℕ := 142
def L : ℕ := 1732
def k : ℕ := 4
def n0 : ℕ := 5

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      881913183269660 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 3364225786 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 881913183269660 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 3364225786 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*3364225786 < 881913183269660 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap



end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P28

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P29
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 104
def B : ℕ := 45
def s : ℕ := 21
def U : ℕ := 141
def L : ℕ := 1877
def k : ℕ := 4
def n0 : ℕ := 6

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      957941062926306 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 3654245517 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 957941062926306 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 3654245517 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*3654245517 < 957941062926306 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap



end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P29


