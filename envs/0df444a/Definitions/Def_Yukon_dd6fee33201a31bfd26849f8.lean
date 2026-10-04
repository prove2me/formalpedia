-- Prove2me | Definitions.Def_Yukon_dd6fee33201a31bfd26849f8
-- name    : Yukon_dd6fee33201a31bfd26849f8
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T08:38:25.219492+00:00
-- url     : https://prove2.me/theorems/fe58efce-e002-4cf2-8355-a212afdb431e
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceLowZ23Counts6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceLowZ23Counts6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceLowZ23Counts6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-0fa592ac43409f0052af279d79d76edd83a6b6fcae6feaedb80065f1f475c226
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNjEwZGIxNTM3OWVhOGQ5ZDU2Mjg1ZThjZjllZDMyNGZjODFmNzI2YTU2YzkxOTE4NjQ3ZDBhMGRlZTE4YTJlYiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtMGZhNTkyYWM0MzQwOWYwMDUyYWYyNzlkNzlkNzZlZGQ4M2E2YjZmY2FlNmZlYWVkYjgwMDY1ZjFmNDc1YzIyNiIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2RkNmZlZTMzMjAxYTMxYmZkMjY4NDlmOCIsInYiOjJ9]

import Definitions.Def_Yukon_f53921b9b22d3fcb96996433

import Definitions.Def_Yukon_e35b4a9947b0b30874d0bba4












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Kernel-checked dimensions for lower-total Z source 23.
Only the existing closed count/rank formulas are evaluated. -/
namespace ProximityPrize.SubmissionLower.MovingSourceLowZ23Counts6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def cutoff (h : ℕ) : ℕ :=
  114*181255-SecondJetRelaxedDifferentiation.reserve 5 7 h*50186

theorem middle_cap (h : ℕ) (_hh : h≤20) : 155≤(cutoff h+45-1)/131071 := by
  unfold cutoff SecondJetRelaxedDifferentiation.reserve
  split_ifs <;> omega

theorem coefficients_value :
    coefficientCount cutoff 131071 3382 45 20 155=2147578068607419 := by
  decide +kernel

theorem rank_value : SecondJetRelaxedCounts.rankBound 114 3382 45 20 155=8192358200 := by
  decide +kernel

theorem source_card : Fintype.card (Index cutoff 131071 3382 45 20 155)=2147578068607419 := by
  rw [card_index_closed cutoff 131071 3382 45 20 155 (by omega),coefficients_value]

theorem source_rank : SecondJetRelaxedGlobalMap.rankBound 114 3382 45 20 155
    (fun h => (cutoff h+45-1)/131071)=8192358200 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed 114 3382 45 20 155 _
    (by omega) (by omega) (by omega) (by omega) middle_cap,rank_value]






end ProximityPrize.SubmissionLower.MovingSourceLowZ23Counts6814


