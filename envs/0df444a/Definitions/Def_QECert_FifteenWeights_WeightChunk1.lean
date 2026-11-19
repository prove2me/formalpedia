-- Prove2me | Definitions.Def_QECert_FifteenWeights_WeightChunk1
-- name    : QECert_FifteenWeights_WeightChunk1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:56:46.667388+00:00
-- url     : https://prove2.me/theorems/19593c15-a421-4bee-8e32-2d18b00f7723
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
private theorem certificate_64 : HammingWeight (l2CoefficientMap (certificateCoefficient 64)) = 4 := by
  decide +kernel
private theorem certificate_65 : HammingWeight (l2CoefficientMap (certificateCoefficient 65)) = 4 := by
  decide +kernel
private theorem certificate_66 : HammingWeight (l2CoefficientMap (certificateCoefficient 66)) = 8 := by
  decide +kernel
private theorem certificate_67 : HammingWeight (l2CoefficientMap (certificateCoefficient 67)) = 8 := by
  decide +kernel
private theorem certificate_68 : HammingWeight (l2CoefficientMap (certificateCoefficient 68)) = 8 := by
  decide +kernel
private theorem certificate_69 : HammingWeight (l2CoefficientMap (certificateCoefficient 69)) = 8 := by
  decide +kernel
private theorem certificate_70 : HammingWeight (l2CoefficientMap (certificateCoefficient 70)) = 8 := by
  decide +kernel
private theorem certificate_71 : HammingWeight (l2CoefficientMap (certificateCoefficient 71)) = 8 := by
  decide +kernel
private theorem certificate_72 : HammingWeight (l2CoefficientMap (certificateCoefficient 72)) = 4 := by
  decide +kernel
private theorem certificate_73 : HammingWeight (l2CoefficientMap (certificateCoefficient 73)) = 12 := by
  decide +kernel
private theorem certificate_74 : HammingWeight (l2CoefficientMap (certificateCoefficient 74)) = 8 := by
  decide +kernel
private theorem certificate_75 : HammingWeight (l2CoefficientMap (certificateCoefficient 75)) = 8 := by
  decide +kernel
private theorem certificate_76 : HammingWeight (l2CoefficientMap (certificateCoefficient 76)) = 8 := by
  decide +kernel
private theorem certificate_77 : HammingWeight (l2CoefficientMap (certificateCoefficient 77)) = 8 := by
  decide +kernel
private theorem certificate_78 : HammingWeight (l2CoefficientMap (certificateCoefficient 78)) = 8 := by
  decide +kernel
private theorem certificate_79 : HammingWeight (l2CoefficientMap (certificateCoefficient 79)) = 8 := by
  decide +kernel
private theorem certificate_80 : HammingWeight (l2CoefficientMap (certificateCoefficient 80)) = 4 := by
  decide +kernel
private theorem certificate_81 : HammingWeight (l2CoefficientMap (certificateCoefficient 81)) = 4 := by
  decide +kernel
private theorem certificate_82 : HammingWeight (l2CoefficientMap (certificateCoefficient 82)) = 8 := by
  decide +kernel
private theorem certificate_83 : HammingWeight (l2CoefficientMap (certificateCoefficient 83)) = 8 := by
  decide +kernel
private theorem certificate_84 : HammingWeight (l2CoefficientMap (certificateCoefficient 84)) = 8 := by
  decide +kernel
private theorem certificate_85 : HammingWeight (l2CoefficientMap (certificateCoefficient 85)) = 8 := by
  decide +kernel
private theorem certificate_86 : HammingWeight (l2CoefficientMap (certificateCoefficient 86)) = 8 := by
  decide +kernel
private theorem certificate_87 : HammingWeight (l2CoefficientMap (certificateCoefficient 87)) = 8 := by
  decide +kernel
private theorem certificate_88 : HammingWeight (l2CoefficientMap (certificateCoefficient 88)) = 8 := by
  decide +kernel
private theorem certificate_89 : HammingWeight (l2CoefficientMap (certificateCoefficient 89)) = 8 := by
  decide +kernel
private theorem certificate_90 : HammingWeight (l2CoefficientMap (certificateCoefficient 90)) = 4 := by
  decide +kernel
private theorem certificate_91 : HammingWeight (l2CoefficientMap (certificateCoefficient 91)) = 12 := by
  decide +kernel
private theorem certificate_92 : HammingWeight (l2CoefficientMap (certificateCoefficient 92)) = 8 := by
  decide +kernel
private theorem certificate_93 : HammingWeight (l2CoefficientMap (certificateCoefficient 93)) = 8 := by
  decide +kernel
private theorem certificate_94 : HammingWeight (l2CoefficientMap (certificateCoefficient 94)) = 8 := by
  decide +kernel
private theorem certificate_95 : HammingWeight (l2CoefficientMap (certificateCoefficient 95)) = 8 := by
  decide +kernel
private theorem certificate_96 : HammingWeight (l2CoefficientMap (certificateCoefficient 96)) = 4 := by
  decide +kernel
private theorem certificate_97 : HammingWeight (l2CoefficientMap (certificateCoefficient 97)) = 4 := by
  decide +kernel
private theorem certificate_98 : HammingWeight (l2CoefficientMap (certificateCoefficient 98)) = 8 := by
  decide +kernel
private theorem certificate_99 : HammingWeight (l2CoefficientMap (certificateCoefficient 99)) = 8 := by
  decide +kernel
private theorem certificate_100 : HammingWeight (l2CoefficientMap (certificateCoefficient 100)) = 8 := by
  decide +kernel
private theorem certificate_101 : HammingWeight (l2CoefficientMap (certificateCoefficient 101)) = 8 := by
  decide +kernel
private theorem certificate_102 : HammingWeight (l2CoefficientMap (certificateCoefficient 102)) = 8 := by
  decide +kernel
private theorem certificate_103 : HammingWeight (l2CoefficientMap (certificateCoefficient 103)) = 8 := by
  decide +kernel
private theorem certificate_104 : HammingWeight (l2CoefficientMap (certificateCoefficient 104)) = 8 := by
  decide +kernel
private theorem certificate_105 : HammingWeight (l2CoefficientMap (certificateCoefficient 105)) = 8 := by
  decide +kernel
private theorem certificate_106 : HammingWeight (l2CoefficientMap (certificateCoefficient 106)) = 8 := by
  decide +kernel
private theorem certificate_107 : HammingWeight (l2CoefficientMap (certificateCoefficient 107)) = 8 := by
  decide +kernel
private theorem certificate_108 : HammingWeight (l2CoefficientMap (certificateCoefficient 108)) = 4 := by
  decide +kernel
private theorem certificate_109 : HammingWeight (l2CoefficientMap (certificateCoefficient 109)) = 12 := by
  decide +kernel
private theorem certificate_110 : HammingWeight (l2CoefficientMap (certificateCoefficient 110)) = 8 := by
  decide +kernel
private theorem certificate_111 : HammingWeight (l2CoefficientMap (certificateCoefficient 111)) = 8 := by
  decide +kernel
private theorem certificate_112 : HammingWeight (l2CoefficientMap (certificateCoefficient 112)) = 4 := by
  decide +kernel
private theorem certificate_113 : HammingWeight (l2CoefficientMap (certificateCoefficient 113)) = 4 := by
  decide +kernel
private theorem certificate_114 : HammingWeight (l2CoefficientMap (certificateCoefficient 114)) = 8 := by
  decide +kernel
private theorem certificate_115 : HammingWeight (l2CoefficientMap (certificateCoefficient 115)) = 8 := by
  decide +kernel
private theorem certificate_116 : HammingWeight (l2CoefficientMap (certificateCoefficient 116)) = 8 := by
  decide +kernel
private theorem certificate_117 : HammingWeight (l2CoefficientMap (certificateCoefficient 117)) = 8 := by
  decide +kernel
private theorem certificate_118 : HammingWeight (l2CoefficientMap (certificateCoefficient 118)) = 8 := by
  decide +kernel
private theorem certificate_119 : HammingWeight (l2CoefficientMap (certificateCoefficient 119)) = 8 := by
  decide +kernel
private theorem certificate_120 : HammingWeight (l2CoefficientMap (certificateCoefficient 120)) = 8 := by
  decide +kernel
private theorem certificate_121 : HammingWeight (l2CoefficientMap (certificateCoefficient 121)) = 8 := by
  decide +kernel
private theorem certificate_122 : HammingWeight (l2CoefficientMap (certificateCoefficient 122)) = 8 := by
  decide +kernel
private theorem certificate_123 : HammingWeight (l2CoefficientMap (certificateCoefficient 123)) = 8 := by
  decide +kernel
private theorem certificate_124 : HammingWeight (l2CoefficientMap (certificateCoefficient 124)) = 8 := by
  decide +kernel
private theorem certificate_125 : HammingWeight (l2CoefficientMap (certificateCoefficient 125)) = 8 := by
  decide +kernel
private theorem certificate_126 : HammingWeight (l2CoefficientMap (certificateCoefficient 126)) = 4 := by
  decide +kernel
private theorem certificate_127 : HammingWeight (l2CoefficientMap (certificateCoefficient 127)) = 12 := by
  decide +kernel
theorem word_table_block_1 (j : Fin 64) : HammingWeight (l2CoefficientMap (certificateCoefficient (1 * 64 + j.val))) = certificateWeightBlock 1 j := by
  change HammingWeight (l2CoefficientMap (certificateCoefficient (1 * 64 + j.val))) = (![4, 4, 8, 8, 8, 8, 8, 8, 4, 12, 8, 8, 8, 8, 8, 8, 4, 4, 8, 8, 8, 8, 8, 8, 8, 8, 4, 12, 8, 8, 8, 8, 4, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 12, 8, 8, 4, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 12] : Fin 64 → Nat) j
  fin_cases j
  · exact certificate_64
  · exact certificate_65
  · exact certificate_66
  · exact certificate_67
  · exact certificate_68
  · exact certificate_69
  · exact certificate_70
  · exact certificate_71
  · exact certificate_72
  · exact certificate_73
  · exact certificate_74
  · exact certificate_75
  · exact certificate_76
  · exact certificate_77
  · exact certificate_78
  · exact certificate_79
  · exact certificate_80
  · exact certificate_81
  · exact certificate_82
  · exact certificate_83
  · exact certificate_84
  · exact certificate_85
  · exact certificate_86
  · exact certificate_87
  · exact certificate_88
  · exact certificate_89
  · exact certificate_90
  · exact certificate_91
  · exact certificate_92
  · exact certificate_93
  · exact certificate_94
  · exact certificate_95
  · exact certificate_96
  · exact certificate_97
  · exact certificate_98
  · exact certificate_99
  · exact certificate_100
  · exact certificate_101
  · exact certificate_102
  · exact certificate_103
  · exact certificate_104
  · exact certificate_105
  · exact certificate_106
  · exact certificate_107
  · exact certificate_108
  · exact certificate_109
  · exact certificate_110
  · exact certificate_111
  · exact certificate_112
  · exact certificate_113
  · exact certificate_114
  · exact certificate_115
  · exact certificate_116
  · exact certificate_117
  · exact certificate_118
  · exact certificate_119
  · exact certificate_120
  · exact certificate_121
  · exact certificate_122
  · exact certificate_123
  · exact certificate_124
  · exact certificate_125
  · exact certificate_126
  · exact certificate_127


end QEC.Distillation.BK15.CertifiedWeights


