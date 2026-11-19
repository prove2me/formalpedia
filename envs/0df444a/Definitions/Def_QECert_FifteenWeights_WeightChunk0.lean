-- Prove2me | Definitions.Def_QECert_FifteenWeights_WeightChunk0
-- name    : QECert_FifteenWeights_WeightChunk0
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:56:28.798341+00:00
-- url     : https://prove2.me/theorems/289d89a5-5daa-4b10-b3c4-070e86cee4eb
-- title:
--   Code
-- statement:
--   Definitions and structural lemmas for Code, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean

import Definitions.Def_QECert_FifteenWeights_CoreWeights
set_option autoImplicit false
set_option maxHeartbeats 200000
open QEC QEC.Coding QEC.Distillation.BK15
open scoped BigOperators
namespace QEC.Distillation.BK15.CertifiedWeights
private theorem certificate_0 : HammingWeight (l2CoefficientMap (certificateCoefficient 0)) = 0 := by
  decide +kernel
private theorem certificate_1 : HammingWeight (l2CoefficientMap (certificateCoefficient 1)) = 8 := by
  decide +kernel
private theorem certificate_2 : HammingWeight (l2CoefficientMap (certificateCoefficient 2)) = 8 := by
  decide +kernel
private theorem certificate_3 : HammingWeight (l2CoefficientMap (certificateCoefficient 3)) = 8 := by
  decide +kernel
private theorem certificate_4 : HammingWeight (l2CoefficientMap (certificateCoefficient 4)) = 8 := by
  decide +kernel
private theorem certificate_5 : HammingWeight (l2CoefficientMap (certificateCoefficient 5)) = 8 := by
  decide +kernel
private theorem certificate_6 : HammingWeight (l2CoefficientMap (certificateCoefficient 6)) = 8 := by
  decide +kernel
private theorem certificate_7 : HammingWeight (l2CoefficientMap (certificateCoefficient 7)) = 8 := by
  decide +kernel
private theorem certificate_8 : HammingWeight (l2CoefficientMap (certificateCoefficient 8)) = 8 := by
  decide +kernel
private theorem certificate_9 : HammingWeight (l2CoefficientMap (certificateCoefficient 9)) = 8 := by
  decide +kernel
private theorem certificate_10 : HammingWeight (l2CoefficientMap (certificateCoefficient 10)) = 8 := by
  decide +kernel
private theorem certificate_11 : HammingWeight (l2CoefficientMap (certificateCoefficient 11)) = 8 := by
  decide +kernel
private theorem certificate_12 : HammingWeight (l2CoefficientMap (certificateCoefficient 12)) = 8 := by
  decide +kernel
private theorem certificate_13 : HammingWeight (l2CoefficientMap (certificateCoefficient 13)) = 8 := by
  decide +kernel
private theorem certificate_14 : HammingWeight (l2CoefficientMap (certificateCoefficient 14)) = 8 := by
  decide +kernel
private theorem certificate_15 : HammingWeight (l2CoefficientMap (certificateCoefficient 15)) = 8 := by
  decide +kernel
private theorem certificate_16 : HammingWeight (l2CoefficientMap (certificateCoefficient 16)) = 4 := by
  decide +kernel
private theorem certificate_17 : HammingWeight (l2CoefficientMap (certificateCoefficient 17)) = 4 := by
  decide +kernel
private theorem certificate_18 : HammingWeight (l2CoefficientMap (certificateCoefficient 18)) = 4 := by
  decide +kernel
private theorem certificate_19 : HammingWeight (l2CoefficientMap (certificateCoefficient 19)) = 12 := by
  decide +kernel
private theorem certificate_20 : HammingWeight (l2CoefficientMap (certificateCoefficient 20)) = 8 := by
  decide +kernel
private theorem certificate_21 : HammingWeight (l2CoefficientMap (certificateCoefficient 21)) = 8 := by
  decide +kernel
private theorem certificate_22 : HammingWeight (l2CoefficientMap (certificateCoefficient 22)) = 8 := by
  decide +kernel
private theorem certificate_23 : HammingWeight (l2CoefficientMap (certificateCoefficient 23)) = 8 := by
  decide +kernel
private theorem certificate_24 : HammingWeight (l2CoefficientMap (certificateCoefficient 24)) = 8 := by
  decide +kernel
private theorem certificate_25 : HammingWeight (l2CoefficientMap (certificateCoefficient 25)) = 8 := by
  decide +kernel
private theorem certificate_26 : HammingWeight (l2CoefficientMap (certificateCoefficient 26)) = 8 := by
  decide +kernel
private theorem certificate_27 : HammingWeight (l2CoefficientMap (certificateCoefficient 27)) = 8 := by
  decide +kernel
private theorem certificate_28 : HammingWeight (l2CoefficientMap (certificateCoefficient 28)) = 8 := by
  decide +kernel
private theorem certificate_29 : HammingWeight (l2CoefficientMap (certificateCoefficient 29)) = 8 := by
  decide +kernel
private theorem certificate_30 : HammingWeight (l2CoefficientMap (certificateCoefficient 30)) = 8 := by
  decide +kernel
private theorem certificate_31 : HammingWeight (l2CoefficientMap (certificateCoefficient 31)) = 8 := by
  decide +kernel
private theorem certificate_32 : HammingWeight (l2CoefficientMap (certificateCoefficient 32)) = 4 := by
  decide +kernel
private theorem certificate_33 : HammingWeight (l2CoefficientMap (certificateCoefficient 33)) = 4 := by
  decide +kernel
private theorem certificate_34 : HammingWeight (l2CoefficientMap (certificateCoefficient 34)) = 8 := by
  decide +kernel
private theorem certificate_35 : HammingWeight (l2CoefficientMap (certificateCoefficient 35)) = 8 := by
  decide +kernel
private theorem certificate_36 : HammingWeight (l2CoefficientMap (certificateCoefficient 36)) = 4 := by
  decide +kernel
private theorem certificate_37 : HammingWeight (l2CoefficientMap (certificateCoefficient 37)) = 12 := by
  decide +kernel
private theorem certificate_38 : HammingWeight (l2CoefficientMap (certificateCoefficient 38)) = 8 := by
  decide +kernel
private theorem certificate_39 : HammingWeight (l2CoefficientMap (certificateCoefficient 39)) = 8 := by
  decide +kernel
private theorem certificate_40 : HammingWeight (l2CoefficientMap (certificateCoefficient 40)) = 8 := by
  decide +kernel
private theorem certificate_41 : HammingWeight (l2CoefficientMap (certificateCoefficient 41)) = 8 := by
  decide +kernel
private theorem certificate_42 : HammingWeight (l2CoefficientMap (certificateCoefficient 42)) = 8 := by
  decide +kernel
private theorem certificate_43 : HammingWeight (l2CoefficientMap (certificateCoefficient 43)) = 8 := by
  decide +kernel
private theorem certificate_44 : HammingWeight (l2CoefficientMap (certificateCoefficient 44)) = 8 := by
  decide +kernel
private theorem certificate_45 : HammingWeight (l2CoefficientMap (certificateCoefficient 45)) = 8 := by
  decide +kernel
private theorem certificate_46 : HammingWeight (l2CoefficientMap (certificateCoefficient 46)) = 8 := by
  decide +kernel
private theorem certificate_47 : HammingWeight (l2CoefficientMap (certificateCoefficient 47)) = 8 := by
  decide +kernel
private theorem certificate_48 : HammingWeight (l2CoefficientMap (certificateCoefficient 48)) = 4 := by
  decide +kernel
private theorem certificate_49 : HammingWeight (l2CoefficientMap (certificateCoefficient 49)) = 4 := by
  decide +kernel
private theorem certificate_50 : HammingWeight (l2CoefficientMap (certificateCoefficient 50)) = 8 := by
  decide +kernel
private theorem certificate_51 : HammingWeight (l2CoefficientMap (certificateCoefficient 51)) = 8 := by
  decide +kernel
private theorem certificate_52 : HammingWeight (l2CoefficientMap (certificateCoefficient 52)) = 8 := by
  decide +kernel
private theorem certificate_53 : HammingWeight (l2CoefficientMap (certificateCoefficient 53)) = 8 := by
  decide +kernel
private theorem certificate_54 : HammingWeight (l2CoefficientMap (certificateCoefficient 54)) = 4 := by
  decide +kernel
private theorem certificate_55 : HammingWeight (l2CoefficientMap (certificateCoefficient 55)) = 12 := by
  decide +kernel
private theorem certificate_56 : HammingWeight (l2CoefficientMap (certificateCoefficient 56)) = 8 := by
  decide +kernel
private theorem certificate_57 : HammingWeight (l2CoefficientMap (certificateCoefficient 57)) = 8 := by
  decide +kernel
private theorem certificate_58 : HammingWeight (l2CoefficientMap (certificateCoefficient 58)) = 8 := by
  decide +kernel
private theorem certificate_59 : HammingWeight (l2CoefficientMap (certificateCoefficient 59)) = 8 := by
  decide +kernel
private theorem certificate_60 : HammingWeight (l2CoefficientMap (certificateCoefficient 60)) = 8 := by
  decide +kernel
private theorem certificate_61 : HammingWeight (l2CoefficientMap (certificateCoefficient 61)) = 8 := by
  decide +kernel
private theorem certificate_62 : HammingWeight (l2CoefficientMap (certificateCoefficient 62)) = 8 := by
  decide +kernel
private theorem certificate_63 : HammingWeight (l2CoefficientMap (certificateCoefficient 63)) = 8 := by
  decide +kernel
theorem word_table_block_0 (j : Fin 64) : HammingWeight (l2CoefficientMap (certificateCoefficient (0 * 64 + j.val))) = certificateWeightBlock 0 j := by
  change HammingWeight (l2CoefficientMap (certificateCoefficient (0 * 64 + j.val))) = (![0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 4, 4, 12, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 4, 8, 8, 4, 12, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 4, 8, 8, 8, 8, 4, 12, 8, 8, 8, 8, 8, 8, 8, 8] : Fin 64 → Nat) j
  fin_cases j
  · exact certificate_0
  · exact certificate_1
  · exact certificate_2
  · exact certificate_3
  · exact certificate_4
  · exact certificate_5
  · exact certificate_6
  · exact certificate_7
  · exact certificate_8
  · exact certificate_9
  · exact certificate_10
  · exact certificate_11
  · exact certificate_12
  · exact certificate_13
  · exact certificate_14
  · exact certificate_15
  · exact certificate_16
  · exact certificate_17
  · exact certificate_18
  · exact certificate_19
  · exact certificate_20
  · exact certificate_21
  · exact certificate_22
  · exact certificate_23
  · exact certificate_24
  · exact certificate_25
  · exact certificate_26
  · exact certificate_27
  · exact certificate_28
  · exact certificate_29
  · exact certificate_30
  · exact certificate_31
  · exact certificate_32
  · exact certificate_33
  · exact certificate_34
  · exact certificate_35
  · exact certificate_36
  · exact certificate_37
  · exact certificate_38
  · exact certificate_39
  · exact certificate_40
  · exact certificate_41
  · exact certificate_42
  · exact certificate_43
  · exact certificate_44
  · exact certificate_45
  · exact certificate_46
  · exact certificate_47
  · exact certificate_48
  · exact certificate_49
  · exact certificate_50
  · exact certificate_51
  · exact certificate_52
  · exact certificate_53
  · exact certificate_54
  · exact certificate_55
  · exact certificate_56
  · exact certificate_57
  · exact certificate_58
  · exact certificate_59
  · exact certificate_60
  · exact certificate_61
  · exact certificate_62
  · exact certificate_63


end QEC.Distillation.BK15.CertifiedWeights


