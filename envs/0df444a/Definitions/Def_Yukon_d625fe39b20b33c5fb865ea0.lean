-- Prove2me | Definitions.Def_Yukon_d625fe39b20b33c5fb865ea0
-- name    : Yukon_d625fe39b20b33c5fb865ea0
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:11:02.264283+00:00
-- url     : https://prove2.me/theorems/4c7d4b7a-5ac3-4141-8f99-5d26277f1295
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberKernels6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberKernels6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberKernels6814.lean
--
--   yukon-proof-operation:foundation-direct-2c4d13933d65e1f7b11c6eebd4772b642b150b9f0dd4121acb4113e2129cf3fc
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYWFkMjQ1MDJmOWY4MmNhNDkzYzFkNDcwZWRhZDZlYjliMTk3NGU1NTRlOWJmZTlhNjBhMmY2N2Y0NzJlMDA5ZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTJjNGQxMzkzM2Q2NWUxZjdiMTFjNmVlYmQ0NzcyYjY0MmIxNTBiOWYwZGQ0MTIxYWNiNDExM2UyMTI5Y2YzZmMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9kNjI1ZmUzOWIyMGIzM2M1ZmI4NjVlYTAiLCJ2IjoyfQ]

import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberKernels6814
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace A
theorem coefficient_exact : coefficientCount 23019385 131071 188820 37 = 11735451064784705 := by
  rw [show 23019385 = 175*131071+81960 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 175 81960 131071 188820 37
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 127 188820 37 = 44767193083 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
end A

namespace B
theorem coefficient_exact : coefficientCount 24288170 131071 35527 40 = 2632290312284855 := by
  rw [show 24288170 = 185*131071+40035 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 185 40035 131071 35527 40
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 134 35527 40 = 10041390565 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
end B

namespace TCap
theorem coefficient_exact : coefficientCount 40963630 131071 10715 70 = 3830032208114182 := by
  rw [show 40963630 = 312*131071+69478 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 312 69478 131071 10715 70
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 226 10715 70 = 14610413086 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 40963630 131071 10715 70 -
    262144*localRankBound 226 10715 70 = 80097798 := by
  norm_num only [coefficient_exact,rank_exact]
end TCap

namespace Source00
theorem coefficient_exact : coefficientCount 11600138745 131071 3840000 19840 = 30710885942172478044882372 := by
  rw [show 11600138745 = 88502*131071+93103 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 88502 93103 131071 3840000 19840
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 63999 3840000 19840 = 116780376202356671680 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 11600138745 131071 3840000 19840 -
    262144*localRankBound 63999 3840000 19840 = 97611002981890704000452 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 97611002981890704000452 ≤ coefficientCount 11600138745 131071 3840000 19840 -
    262144*localRankBound 63999 3840000 19840 := by rw [nullity_exact]
theorem shape : 11600138745+19840 ≤ 131071*(88502+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    97611002981890704000452 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 11600138745 131071 3840000 19840 63999
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    11600138745 3840000 19840 63999 97611002981890704000452 u0 u1 nullity_lower


end Source00

namespace Source01
theorem coefficient_exact : coefficientCount 5800160000 131071 3200000 9888 = 3203463451585968200302508 := by
  rw [show 5800160000 = 44252*131071+6108 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44252 6108 131071 3200000 9888
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 32000 3200000 9888 = 12172764924613929328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 5800160000 131071 3200000 9888 -
    262144*localRankBound 32000 3200000 9888 = 12446163187974310543276 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 12446163187974310543276 ≤ coefficientCount 5800160000 131071 3200000 9888 -
    262144*localRankBound 32000 3200000 9888 := by rw [nullity_exact]
theorem shape : 5800160000+9888 ≤ 131071*(44252+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    12446163187974310543276 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5800160000 131071 3200000 9888 32000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    5800160000 3200000 9888 32000 12446163187974310543276 u0 u1 nullity_lower


end Source01

namespace Source02
theorem coefficient_exact : coefficientCount 5800160000 131071 2880000 9888 = 2881328209975535379182508 := by
  rw [show 5800160000 = 44252*131071+6108 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44252 6108 131071 2880000 9888
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 32000 2880000 9888 = 10950008283031849328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 5800160000 131071 2880000 9888 -
    262144*localRankBound 32000 2880000 9888 = 10849238628434268943276 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 10849238628434268943276 ≤ coefficientCount 5800160000 131071 2880000 9888 -
    262144*localRankBound 32000 2880000 9888 := by rw [nullity_exact]
theorem shape : 5800160000+9888 ≤ 131071*(44252+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    10849238628434268943276 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5800160000 131071 2880000 9888 32000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    5800160000 2880000 9888 32000 10849238628434268943276 u0 u1 nullity_lower


end Source02

namespace Source03
theorem coefficient_exact : coefficientCount 2900080000 131071 1062000 4940 = 132453331603463105912295 := by
  rw [show 2900080000 = 22126*131071+3054 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 22126 3054 131071 1062000 4940
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 16000 1062000 4940 = 503593395806461590 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 2900080000 131071 1062000 4940 -
    262144*localRankBound 16000 1062000 4940 = 439344453174038863335 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 439344453174038863335 ≤ coefficientCount 2900080000 131071 1062000 4940 -
    262144*localRankBound 16000 1062000 4940 := by rw [nullity_exact]
theorem shape : 2900080000+4940 ≤ 131071*(22126+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    439344453174038863335 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2900080000 131071 1062000 4940 16000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    2900080000 1062000 4940 16000 439344453174038863335 u0 u1 nullity_lower


end Source03

namespace Source04
theorem coefficient_exact : coefficientCount 1450040000 131071 531000 2470 = 8280456122368111344278 := by
  rw [show 1450040000 = 11063*131071+1527 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 11063 1527 131071 531000 2470
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 8000 531000 2470 = 31483869872329770 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 1450040000 131071 531000 2470 -
    262144*localRankBound 8000 531000 2470 = 27148538556096117398 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 27148538556096117398 ≤ coefficientCount 1450040000 131071 531000 2470 -
    262144*localRankBound 8000 531000 2470 := by rw [nullity_exact]
theorem shape : 1450040000+2470 ≤ 131071*(11063+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    27148538556096117398 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 1450040000 131071 531000 2470 8000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    1450040000 531000 2470 8000 27148538556096117398 u0 u1 nullity_lower


end Source04

namespace Source05
theorem coefficient_exact : coefficientCount 181255000 131071 88902 308 = 2718217191936342235 := by
  rw [show 181255000 = 1382*131071+114878 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 1382 114878 131071 88902 308
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 1000 88902 308 = 10336494078526 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 181255000 131071 88902 308 -
    262144*localRankBound 1000 88902 308 = 8567288215222491 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 8567288215222491 ≤ coefficientCount 181255000 131071 88902 308 -
    262144*localRankBound 1000 88902 308 := by rw [nullity_exact]
theorem shape : 181255000+308 ≤ 131071*(1382+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    8567288215222491 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 181255000 131071 88902 308 1000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    181255000 88902 308 1000 8567288215222491 u0 u1 nullity_lower


end Source05

namespace Source06
theorem coefficient_exact : coefficientCount 2537570000 131071 3640000 4267 = 303057670116901727221315 := by
  rw [show 2537570000 = 19360*131071+35440 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 19360 35440 131071 3640000 4267
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 14000 3640000 4267 = 1150877542707512224 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 2537570000 131071 3640000 4267 -
    262144*localRankBound 14000 3640000 4267 = 1362027561383642773059 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1362027561383642773059 ≤ coefficientCount 2537570000 131071 3640000 4267 -
    262144*localRankBound 14000 3640000 4267 := by rw [nullity_exact]
theorem shape : 2537570000+4267 ≤ 131071*(19360+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1362027561383642773059 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2537570000 131071 3640000 4267 14000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    2537570000 3640000 4267 14000 1362027561383642773059 u0 u1 nullity_lower


end Source06

namespace TCap
theorem quotient_count_exact : coefficientCount 40963630 131071 0 70 = 40963630 := by decide +kernel
theorem quotient_count_lt : coefficientCount 40963630 131071 0 70 < 80097798 := by
  rw [quotient_count_exact]
  decide +kernel
end TCap

end ProximityPrize.SubmissionLower.MovingFiberKernels6814


