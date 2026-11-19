-- Prove2me | Definitions.Def_QECert_FifteenWeights_WeightChunk2
-- name    : QECert_FifteenWeights_WeightChunk2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:56:48.108198+00:00
-- url     : https://prove2.me/theorems/6a7a55cc-22cf-48b7-95b3-aaafcec7dbc6
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
private theorem certificate_128 : HammingWeight (l2CoefficientMap (certificateCoefficient 128)) = 4 := by
  decide +kernel
private theorem certificate_129 : HammingWeight (l2CoefficientMap (certificateCoefficient 129)) = 8 := by
  decide +kernel
private theorem certificate_130 : HammingWeight (l2CoefficientMap (certificateCoefficient 130)) = 4 := by
  decide +kernel
private theorem certificate_131 : HammingWeight (l2CoefficientMap (certificateCoefficient 131)) = 8 := by
  decide +kernel
private theorem certificate_132 : HammingWeight (l2CoefficientMap (certificateCoefficient 132)) = 4 := by
  decide +kernel
private theorem certificate_133 : HammingWeight (l2CoefficientMap (certificateCoefficient 133)) = 8 := by
  decide +kernel
private theorem certificate_134 : HammingWeight (l2CoefficientMap (certificateCoefficient 134)) = 12 := by
  decide +kernel
private theorem certificate_135 : HammingWeight (l2CoefficientMap (certificateCoefficient 135)) = 8 := by
  decide +kernel
private theorem certificate_136 : HammingWeight (l2CoefficientMap (certificateCoefficient 136)) = 8 := by
  decide +kernel
private theorem certificate_137 : HammingWeight (l2CoefficientMap (certificateCoefficient 137)) = 8 := by
  decide +kernel
private theorem certificate_138 : HammingWeight (l2CoefficientMap (certificateCoefficient 138)) = 8 := by
  decide +kernel
private theorem certificate_139 : HammingWeight (l2CoefficientMap (certificateCoefficient 139)) = 8 := by
  decide +kernel
private theorem certificate_140 : HammingWeight (l2CoefficientMap (certificateCoefficient 140)) = 8 := by
  decide +kernel
private theorem certificate_141 : HammingWeight (l2CoefficientMap (certificateCoefficient 141)) = 8 := by
  decide +kernel
private theorem certificate_142 : HammingWeight (l2CoefficientMap (certificateCoefficient 142)) = 8 := by
  decide +kernel
private theorem certificate_143 : HammingWeight (l2CoefficientMap (certificateCoefficient 143)) = 8 := by
  decide +kernel
private theorem certificate_144 : HammingWeight (l2CoefficientMap (certificateCoefficient 144)) = 4 := by
  decide +kernel
private theorem certificate_145 : HammingWeight (l2CoefficientMap (certificateCoefficient 145)) = 8 := by
  decide +kernel
private theorem certificate_146 : HammingWeight (l2CoefficientMap (certificateCoefficient 146)) = 4 := by
  decide +kernel
private theorem certificate_147 : HammingWeight (l2CoefficientMap (certificateCoefficient 147)) = 8 := by
  decide +kernel
private theorem certificate_148 : HammingWeight (l2CoefficientMap (certificateCoefficient 148)) = 8 := by
  decide +kernel
private theorem certificate_149 : HammingWeight (l2CoefficientMap (certificateCoefficient 149)) = 4 := by
  decide +kernel
private theorem certificate_150 : HammingWeight (l2CoefficientMap (certificateCoefficient 150)) = 8 := by
  decide +kernel
private theorem certificate_151 : HammingWeight (l2CoefficientMap (certificateCoefficient 151)) = 12 := by
  decide +kernel
private theorem certificate_152 : HammingWeight (l2CoefficientMap (certificateCoefficient 152)) = 8 := by
  decide +kernel
private theorem certificate_153 : HammingWeight (l2CoefficientMap (certificateCoefficient 153)) = 8 := by
  decide +kernel
private theorem certificate_154 : HammingWeight (l2CoefficientMap (certificateCoefficient 154)) = 8 := by
  decide +kernel
private theorem certificate_155 : HammingWeight (l2CoefficientMap (certificateCoefficient 155)) = 8 := by
  decide +kernel
private theorem certificate_156 : HammingWeight (l2CoefficientMap (certificateCoefficient 156)) = 8 := by
  decide +kernel
private theorem certificate_157 : HammingWeight (l2CoefficientMap (certificateCoefficient 157)) = 8 := by
  decide +kernel
private theorem certificate_158 : HammingWeight (l2CoefficientMap (certificateCoefficient 158)) = 8 := by
  decide +kernel
private theorem certificate_159 : HammingWeight (l2CoefficientMap (certificateCoefficient 159)) = 8 := by
  decide +kernel
private theorem certificate_160 : HammingWeight (l2CoefficientMap (certificateCoefficient 160)) = 4 := by
  decide +kernel
private theorem certificate_161 : HammingWeight (l2CoefficientMap (certificateCoefficient 161)) = 8 := by
  decide +kernel
private theorem certificate_162 : HammingWeight (l2CoefficientMap (certificateCoefficient 162)) = 8 := by
  decide +kernel
private theorem certificate_163 : HammingWeight (l2CoefficientMap (certificateCoefficient 163)) = 4 := by
  decide +kernel
private theorem certificate_164 : HammingWeight (l2CoefficientMap (certificateCoefficient 164)) = 4 := by
  decide +kernel
private theorem certificate_165 : HammingWeight (l2CoefficientMap (certificateCoefficient 165)) = 8 := by
  decide +kernel
private theorem certificate_166 : HammingWeight (l2CoefficientMap (certificateCoefficient 166)) = 8 := by
  decide +kernel
private theorem certificate_167 : HammingWeight (l2CoefficientMap (certificateCoefficient 167)) = 12 := by
  decide +kernel
private theorem certificate_168 : HammingWeight (l2CoefficientMap (certificateCoefficient 168)) = 8 := by
  decide +kernel
private theorem certificate_169 : HammingWeight (l2CoefficientMap (certificateCoefficient 169)) = 8 := by
  decide +kernel
private theorem certificate_170 : HammingWeight (l2CoefficientMap (certificateCoefficient 170)) = 8 := by
  decide +kernel
private theorem certificate_171 : HammingWeight (l2CoefficientMap (certificateCoefficient 171)) = 8 := by
  decide +kernel
private theorem certificate_172 : HammingWeight (l2CoefficientMap (certificateCoefficient 172)) = 8 := by
  decide +kernel
private theorem certificate_173 : HammingWeight (l2CoefficientMap (certificateCoefficient 173)) = 8 := by
  decide +kernel
private theorem certificate_174 : HammingWeight (l2CoefficientMap (certificateCoefficient 174)) = 8 := by
  decide +kernel
private theorem certificate_175 : HammingWeight (l2CoefficientMap (certificateCoefficient 175)) = 8 := by
  decide +kernel
private theorem certificate_176 : HammingWeight (l2CoefficientMap (certificateCoefficient 176)) = 8 := by
  decide +kernel
private theorem certificate_177 : HammingWeight (l2CoefficientMap (certificateCoefficient 177)) = 4 := by
  decide +kernel
private theorem certificate_178 : HammingWeight (l2CoefficientMap (certificateCoefficient 178)) = 4 := by
  decide +kernel
private theorem certificate_179 : HammingWeight (l2CoefficientMap (certificateCoefficient 179)) = 8 := by
  decide +kernel
private theorem certificate_180 : HammingWeight (l2CoefficientMap (certificateCoefficient 180)) = 4 := by
  decide +kernel
private theorem certificate_181 : HammingWeight (l2CoefficientMap (certificateCoefficient 181)) = 8 := by
  decide +kernel
private theorem certificate_182 : HammingWeight (l2CoefficientMap (certificateCoefficient 182)) = 8 := by
  decide +kernel
private theorem certificate_183 : HammingWeight (l2CoefficientMap (certificateCoefficient 183)) = 12 := by
  decide +kernel
private theorem certificate_184 : HammingWeight (l2CoefficientMap (certificateCoefficient 184)) = 8 := by
  decide +kernel
private theorem certificate_185 : HammingWeight (l2CoefficientMap (certificateCoefficient 185)) = 8 := by
  decide +kernel
private theorem certificate_186 : HammingWeight (l2CoefficientMap (certificateCoefficient 186)) = 8 := by
  decide +kernel
private theorem certificate_187 : HammingWeight (l2CoefficientMap (certificateCoefficient 187)) = 8 := by
  decide +kernel
private theorem certificate_188 : HammingWeight (l2CoefficientMap (certificateCoefficient 188)) = 8 := by
  decide +kernel
private theorem certificate_189 : HammingWeight (l2CoefficientMap (certificateCoefficient 189)) = 8 := by
  decide +kernel
private theorem certificate_190 : HammingWeight (l2CoefficientMap (certificateCoefficient 190)) = 8 := by
  decide +kernel
private theorem certificate_191 : HammingWeight (l2CoefficientMap (certificateCoefficient 191)) = 8 := by
  decide +kernel
theorem word_table_block_2 (j : Fin 64) : HammingWeight (l2CoefficientMap (certificateCoefficient (2 * 64 + j.val))) = certificateWeightBlock 2 j := by
  change HammingWeight (l2CoefficientMap (certificateCoefficient (2 * 64 + j.val))) = (![4, 8, 4, 8, 4, 8, 12, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 8, 4, 8, 8, 4, 8, 12, 8, 8, 8, 8, 8, 8, 8, 8, 4, 8, 8, 4, 4, 8, 8, 12, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 4, 8, 4, 8, 8, 12, 8, 8, 8, 8, 8, 8, 8, 8] : Fin 64 → Nat) j
  fin_cases j
  · exact certificate_128
  · exact certificate_129
  · exact certificate_130
  · exact certificate_131
  · exact certificate_132
  · exact certificate_133
  · exact certificate_134
  · exact certificate_135
  · exact certificate_136
  · exact certificate_137
  · exact certificate_138
  · exact certificate_139
  · exact certificate_140
  · exact certificate_141
  · exact certificate_142
  · exact certificate_143
  · exact certificate_144
  · exact certificate_145
  · exact certificate_146
  · exact certificate_147
  · exact certificate_148
  · exact certificate_149
  · exact certificate_150
  · exact certificate_151
  · exact certificate_152
  · exact certificate_153
  · exact certificate_154
  · exact certificate_155
  · exact certificate_156
  · exact certificate_157
  · exact certificate_158
  · exact certificate_159
  · exact certificate_160
  · exact certificate_161
  · exact certificate_162
  · exact certificate_163
  · exact certificate_164
  · exact certificate_165
  · exact certificate_166
  · exact certificate_167
  · exact certificate_168
  · exact certificate_169
  · exact certificate_170
  · exact certificate_171
  · exact certificate_172
  · exact certificate_173
  · exact certificate_174
  · exact certificate_175
  · exact certificate_176
  · exact certificate_177
  · exact certificate_178
  · exact certificate_179
  · exact certificate_180
  · exact certificate_181
  · exact certificate_182
  · exact certificate_183
  · exact certificate_184
  · exact certificate_185
  · exact certificate_186
  · exact certificate_187
  · exact certificate_188
  · exact certificate_189
  · exact certificate_190
  · exact certificate_191


end QEC.Distillation.BK15.CertifiedWeights


