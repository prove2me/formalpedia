-- Prove2me | Definitions.Def_QECert_FifteenWeights_WeightChunk3
-- name    : QECert_FifteenWeights_WeightChunk3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:56:42.803297+00:00
-- url     : https://prove2.me/theorems/5573c99a-1f08-4895-b1e0-6f3f979abe6b
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
private theorem certificate_192 : HammingWeight (l2CoefficientMap (certificateCoefficient 192)) = 6 := by
  decide +kernel
private theorem certificate_193 : HammingWeight (l2CoefficientMap (certificateCoefficient 193)) = 6 := by
  decide +kernel
private theorem certificate_194 : HammingWeight (l2CoefficientMap (certificateCoefficient 194)) = 6 := by
  decide +kernel
private theorem certificate_195 : HammingWeight (l2CoefficientMap (certificateCoefficient 195)) = 6 := by
  decide +kernel
private theorem certificate_196 : HammingWeight (l2CoefficientMap (certificateCoefficient 196)) = 6 := by
  decide +kernel
private theorem certificate_197 : HammingWeight (l2CoefficientMap (certificateCoefficient 197)) = 6 := by
  decide +kernel
private theorem certificate_198 : HammingWeight (l2CoefficientMap (certificateCoefficient 198)) = 10 := by
  decide +kernel
private theorem certificate_199 : HammingWeight (l2CoefficientMap (certificateCoefficient 199)) = 10 := by
  decide +kernel
private theorem certificate_200 : HammingWeight (l2CoefficientMap (certificateCoefficient 200)) = 6 := by
  decide +kernel
private theorem certificate_201 : HammingWeight (l2CoefficientMap (certificateCoefficient 201)) = 10 := by
  decide +kernel
private theorem certificate_202 : HammingWeight (l2CoefficientMap (certificateCoefficient 202)) = 6 := by
  decide +kernel
private theorem certificate_203 : HammingWeight (l2CoefficientMap (certificateCoefficient 203)) = 10 := by
  decide +kernel
private theorem certificate_204 : HammingWeight (l2CoefficientMap (certificateCoefficient 204)) = 6 := by
  decide +kernel
private theorem certificate_205 : HammingWeight (l2CoefficientMap (certificateCoefficient 205)) = 10 := by
  decide +kernel
private theorem certificate_206 : HammingWeight (l2CoefficientMap (certificateCoefficient 206)) = 10 := by
  decide +kernel
private theorem certificate_207 : HammingWeight (l2CoefficientMap (certificateCoefficient 207)) = 6 := by
  decide +kernel
private theorem certificate_208 : HammingWeight (l2CoefficientMap (certificateCoefficient 208)) = 6 := by
  decide +kernel
private theorem certificate_209 : HammingWeight (l2CoefficientMap (certificateCoefficient 209)) = 6 := by
  decide +kernel
private theorem certificate_210 : HammingWeight (l2CoefficientMap (certificateCoefficient 210)) = 6 := by
  decide +kernel
private theorem certificate_211 : HammingWeight (l2CoefficientMap (certificateCoefficient 211)) = 6 := by
  decide +kernel
private theorem certificate_212 : HammingWeight (l2CoefficientMap (certificateCoefficient 212)) = 6 := by
  decide +kernel
private theorem certificate_213 : HammingWeight (l2CoefficientMap (certificateCoefficient 213)) = 6 := by
  decide +kernel
private theorem certificate_214 : HammingWeight (l2CoefficientMap (certificateCoefficient 214)) = 10 := by
  decide +kernel
private theorem certificate_215 : HammingWeight (l2CoefficientMap (certificateCoefficient 215)) = 10 := by
  decide +kernel
private theorem certificate_216 : HammingWeight (l2CoefficientMap (certificateCoefficient 216)) = 6 := by
  decide +kernel
private theorem certificate_217 : HammingWeight (l2CoefficientMap (certificateCoefficient 217)) = 10 := by
  decide +kernel
private theorem certificate_218 : HammingWeight (l2CoefficientMap (certificateCoefficient 218)) = 6 := by
  decide +kernel
private theorem certificate_219 : HammingWeight (l2CoefficientMap (certificateCoefficient 219)) = 10 := by
  decide +kernel
private theorem certificate_220 : HammingWeight (l2CoefficientMap (certificateCoefficient 220)) = 10 := by
  decide +kernel
private theorem certificate_221 : HammingWeight (l2CoefficientMap (certificateCoefficient 221)) = 6 := by
  decide +kernel
private theorem certificate_222 : HammingWeight (l2CoefficientMap (certificateCoefficient 222)) = 6 := by
  decide +kernel
private theorem certificate_223 : HammingWeight (l2CoefficientMap (certificateCoefficient 223)) = 10 := by
  decide +kernel
private theorem certificate_224 : HammingWeight (l2CoefficientMap (certificateCoefficient 224)) = 6 := by
  decide +kernel
private theorem certificate_225 : HammingWeight (l2CoefficientMap (certificateCoefficient 225)) = 6 := by
  decide +kernel
private theorem certificate_226 : HammingWeight (l2CoefficientMap (certificateCoefficient 226)) = 6 := by
  decide +kernel
private theorem certificate_227 : HammingWeight (l2CoefficientMap (certificateCoefficient 227)) = 6 := by
  decide +kernel
private theorem certificate_228 : HammingWeight (l2CoefficientMap (certificateCoefficient 228)) = 6 := by
  decide +kernel
private theorem certificate_229 : HammingWeight (l2CoefficientMap (certificateCoefficient 229)) = 6 := by
  decide +kernel
private theorem certificate_230 : HammingWeight (l2CoefficientMap (certificateCoefficient 230)) = 10 := by
  decide +kernel
private theorem certificate_231 : HammingWeight (l2CoefficientMap (certificateCoefficient 231)) = 10 := by
  decide +kernel
private theorem certificate_232 : HammingWeight (l2CoefficientMap (certificateCoefficient 232)) = 6 := by
  decide +kernel
private theorem certificate_233 : HammingWeight (l2CoefficientMap (certificateCoefficient 233)) = 10 := by
  decide +kernel
private theorem certificate_234 : HammingWeight (l2CoefficientMap (certificateCoefficient 234)) = 10 := by
  decide +kernel
private theorem certificate_235 : HammingWeight (l2CoefficientMap (certificateCoefficient 235)) = 6 := by
  decide +kernel
private theorem certificate_236 : HammingWeight (l2CoefficientMap (certificateCoefficient 236)) = 6 := by
  decide +kernel
private theorem certificate_237 : HammingWeight (l2CoefficientMap (certificateCoefficient 237)) = 10 := by
  decide +kernel
private theorem certificate_238 : HammingWeight (l2CoefficientMap (certificateCoefficient 238)) = 6 := by
  decide +kernel
private theorem certificate_239 : HammingWeight (l2CoefficientMap (certificateCoefficient 239)) = 10 := by
  decide +kernel
private theorem certificate_240 : HammingWeight (l2CoefficientMap (certificateCoefficient 240)) = 6 := by
  decide +kernel
private theorem certificate_241 : HammingWeight (l2CoefficientMap (certificateCoefficient 241)) = 6 := by
  decide +kernel
private theorem certificate_242 : HammingWeight (l2CoefficientMap (certificateCoefficient 242)) = 6 := by
  decide +kernel
private theorem certificate_243 : HammingWeight (l2CoefficientMap (certificateCoefficient 243)) = 6 := by
  decide +kernel
private theorem certificate_244 : HammingWeight (l2CoefficientMap (certificateCoefficient 244)) = 6 := by
  decide +kernel
private theorem certificate_245 : HammingWeight (l2CoefficientMap (certificateCoefficient 245)) = 6 := by
  decide +kernel
private theorem certificate_246 : HammingWeight (l2CoefficientMap (certificateCoefficient 246)) = 10 := by
  decide +kernel
private theorem certificate_247 : HammingWeight (l2CoefficientMap (certificateCoefficient 247)) = 10 := by
  decide +kernel
private theorem certificate_248 : HammingWeight (l2CoefficientMap (certificateCoefficient 248)) = 10 := by
  decide +kernel
private theorem certificate_249 : HammingWeight (l2CoefficientMap (certificateCoefficient 249)) = 6 := by
  decide +kernel
private theorem certificate_250 : HammingWeight (l2CoefficientMap (certificateCoefficient 250)) = 6 := by
  decide +kernel
private theorem certificate_251 : HammingWeight (l2CoefficientMap (certificateCoefficient 251)) = 10 := by
  decide +kernel
private theorem certificate_252 : HammingWeight (l2CoefficientMap (certificateCoefficient 252)) = 6 := by
  decide +kernel
private theorem certificate_253 : HammingWeight (l2CoefficientMap (certificateCoefficient 253)) = 10 := by
  decide +kernel
private theorem certificate_254 : HammingWeight (l2CoefficientMap (certificateCoefficient 254)) = 6 := by
  decide +kernel
private theorem certificate_255 : HammingWeight (l2CoefficientMap (certificateCoefficient 255)) = 10 := by
  decide +kernel
theorem word_table_block_3 (j : Fin 64) : HammingWeight (l2CoefficientMap (certificateCoefficient (3 * 64 + j.val))) = certificateWeightBlock 3 j := by
  change HammingWeight (l2CoefficientMap (certificateCoefficient (3 * 64 + j.val))) = (![6, 6, 6, 6, 6, 6, 10, 10, 6, 10, 6, 10, 6, 10, 10, 6, 6, 6, 6, 6, 6, 6, 10, 10, 6, 10, 6, 10, 10, 6, 6, 10, 6, 6, 6, 6, 6, 6, 10, 10, 6, 10, 10, 6, 6, 10, 6, 10, 6, 6, 6, 6, 6, 6, 10, 10, 10, 6, 6, 10, 6, 10, 6, 10] : Fin 64 → Nat) j
  fin_cases j
  · exact certificate_192
  · exact certificate_193
  · exact certificate_194
  · exact certificate_195
  · exact certificate_196
  · exact certificate_197
  · exact certificate_198
  · exact certificate_199
  · exact certificate_200
  · exact certificate_201
  · exact certificate_202
  · exact certificate_203
  · exact certificate_204
  · exact certificate_205
  · exact certificate_206
  · exact certificate_207
  · exact certificate_208
  · exact certificate_209
  · exact certificate_210
  · exact certificate_211
  · exact certificate_212
  · exact certificate_213
  · exact certificate_214
  · exact certificate_215
  · exact certificate_216
  · exact certificate_217
  · exact certificate_218
  · exact certificate_219
  · exact certificate_220
  · exact certificate_221
  · exact certificate_222
  · exact certificate_223
  · exact certificate_224
  · exact certificate_225
  · exact certificate_226
  · exact certificate_227
  · exact certificate_228
  · exact certificate_229
  · exact certificate_230
  · exact certificate_231
  · exact certificate_232
  · exact certificate_233
  · exact certificate_234
  · exact certificate_235
  · exact certificate_236
  · exact certificate_237
  · exact certificate_238
  · exact certificate_239
  · exact certificate_240
  · exact certificate_241
  · exact certificate_242
  · exact certificate_243
  · exact certificate_244
  · exact certificate_245
  · exact certificate_246
  · exact certificate_247
  · exact certificate_248
  · exact certificate_249
  · exact certificate_250
  · exact certificate_251
  · exact certificate_252
  · exact certificate_253
  · exact certificate_254
  · exact certificate_255


end QEC.Distillation.BK15.CertifiedWeights


