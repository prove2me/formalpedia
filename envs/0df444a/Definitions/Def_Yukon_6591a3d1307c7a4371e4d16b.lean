-- Prove2me | Definitions.Def_Yukon_6591a3d1307c7a4371e4d16b
-- name    : Yukon_6591a3d1307c7a4371e4d16b
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T22:09:31.583842+00:00
-- url     : https://prove2.me/theorems/8c9fec1c-96bf-46ba-ba11-6cf5c0a4ff5f
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.WholeSpaceSourceCounts6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.WholeSpaceSourceCounts6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/WholeSpaceSourceCounts6814.lean
--
--   yukon-proof-operation:certificate-split-f46261c5a4480e740efebf85fd01524b5cb5f611e82be04e9faf591172630cf0
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiY2IzMmZhNDQ3NTkwNDZkOWNlZTNkYjk5MzQyZThjNzBlOGNmYmFmY2Q0ZDBhMTAzNDFiZWQ2ZjNmNWQ1ZWE4YiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LWY0NjI2MWM1YTQ0ODBlNzQwZWZlYmY4NWZkMDE1MjRiNWNiNWY2MTFlODJiZTA0ZTlmYWY1OTExNzI2MzBjZjAiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl82NTkxYTNkMTMwN2M3YTQzNzFlNGQxNmIiLCJ2IjoyfQ]

import Definitions.Def_Yukon_9e6b0bff61d8a97ca7ca80a3











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Concrete dimensions for the single enlarged second-jet source.
Only the closed counting formulas are evaluated; the finite polynomial
space itself (208 trillion coefficients) is never enumerated. -/
namespace ProximityPrize.SubmissionLower.WholeSpaceSourceCounts6814
open scoped BigOperators
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def cutoff (h : ℕ) : ℕ :=
  72*181255-SecondJetRelaxedDifferentiation.reserve 2 3 h*50186

theorem middle_cap (h : ℕ) (hh : h ≤ 14) : 98 ≤ (cutoff h+31-1)/131071 := by
  unfold cutoff SecondJetRelaxedDifferentiation.reserve
  split_ifs <;> omega

theorem coefficients_value :
    coefficientCount cutoff 131071 1700 31 14 98=208109695383786 := by
  decide +kernel

theorem rank_value :
    SecondJetRelaxedCounts.rankBound 72 1700 31 14 98=791483658 := by
  decide +kernel

theorem source_card :
    Fintype.card (Index cutoff 131071 1700 31 14 98)=208109695383786 := by
  rw [card_index_closed cutoff 131071 1700 31 14 98 (by omega),coefficients_value]

theorem source_rank :
    SecondJetRelaxedGlobalMap.rankBound 72 1700 31 14 98
      (fun h => (cutoff h+31-1)/131071)=791483658 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed 72 1700 31 14 98 _
    (by omega) (by omega) (by omega) (by omega) middle_cap,rank_value]

theorem source_nullity :
    627003341034+262144*SecondJetRelaxedGlobalMap.rankBound 72 1700 31 14 98
      (fun h => (cutoff h+31-1)/131071) ≤
        Fintype.card (Index cutoff 131071 1700 31 14 98) := by
  rw [source_rank,source_card]



end ProximityPrize.SubmissionLower.WholeSpaceSourceCounts6814


