-- Prove2me | Definitions.Def_Yukon_07741ea792ed852a92883bac
-- name    : Yukon_07741ea792ed852a92883bac
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T20:11:02.975307+00:00
-- url     : https://prove2.me/theorems/c7d0efe5-bde1-4955-9673-ef61f100d0d2
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceLowZ25Counts6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceLowZ25Counts6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceLowZ25Counts6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-a405816ca8076fdbd0708515607503516dc9b0a3523a1d286775cb8eaffaa6b9
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOWQ2OWQ0YjQ2M2QzZWI0YzAxMGRiNzQ5NzgzODBjMDlmODVmNWZmMjQ3MmY2MzE1MjFiOTJjOGJkZDRiZDE2NiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtYTQwNTgxNmNhODA3NmZkYmQwNzA4NTE1NjA3NTAzNTE2ZGM5YjBhMzUyM2ExZDI4Njc3NWNiOGVhZmZhYTZiOSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzA3NzQxZWE3OTJlZDg1MmE5Mjg4M2JhYyIsInYiOjJ9]

import Definitions.Def_Yukon_f53921b9b22d3fcb96996433

import Definitions.Def_Yukon_bde15872549fe2e284917a6b












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Kernel-checked dimensions for lower-total Z source 25.
Only the existing closed count/rank formulas are evaluated. -/
namespace ProximityPrize.SubmissionLower.MovingSourceLowZ25Counts6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def cutoff (h : ℕ) : ℕ :=
  111*181255-SecondJetRelaxedDifferentiation.reserve 5 7 h*50186

theorem middle_cap (h : ℕ) (_hh : h≤21) : 151≤(cutoff h+46-1)/131071 := by
  unfold cutoff SecondJetRelaxedDifferentiation.reserve
  split_ifs <;> omega

theorem coefficients_value :
    coefficientCount cutoff 131071 3411 46 21 151=2116605519616735 := by
  decide +kernel

theorem rank_value : SecondJetRelaxedCounts.rankBound 111 3411 46 21 151=8074209199 := by
  decide +kernel

theorem source_card : Fintype.card (Index cutoff 131071 3411 46 21 151)=2116605519616735 := by
  rw [card_index_closed cutoff 131071 3411 46 21 151 (by omega),coefficients_value]

theorem source_rank : SecondJetRelaxedGlobalMap.rankBound 111 3411 46 21 151
    (fun h => (cutoff h+46-1)/131071)=8074209199 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed 111 3411 46 21 151 _
    (by omega) (by omega) (by omega) (by omega) middle_cap,rank_value]






end ProximityPrize.SubmissionLower.MovingSourceLowZ25Counts6814


