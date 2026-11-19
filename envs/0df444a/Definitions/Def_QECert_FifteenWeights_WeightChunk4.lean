-- Prove2me | Definitions.Def_QECert_FifteenWeights_WeightChunk4
-- name    : QECert_FifteenWeights_WeightChunk4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:57:14.848803+00:00
-- url     : https://prove2.me/theorems/b242f5de-1888-4a56-859d-e9bcef0826fa
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
private theorem certificate_256 : HammingWeight (l2CoefficientMap (certificateCoefficient 256)) = 4 := by
  decide +kernel
private theorem certificate_257 : HammingWeight (l2CoefficientMap (certificateCoefficient 257)) = 8 := by
  decide +kernel
private theorem certificate_258 : HammingWeight (l2CoefficientMap (certificateCoefficient 258)) = 4 := by
  decide +kernel
private theorem certificate_259 : HammingWeight (l2CoefficientMap (certificateCoefficient 259)) = 8 := by
  decide +kernel
private theorem certificate_260 : HammingWeight (l2CoefficientMap (certificateCoefficient 260)) = 8 := by
  decide +kernel
private theorem certificate_261 : HammingWeight (l2CoefficientMap (certificateCoefficient 261)) = 8 := by
  decide +kernel
private theorem certificate_262 : HammingWeight (l2CoefficientMap (certificateCoefficient 262)) = 8 := by
  decide +kernel
private theorem certificate_263 : HammingWeight (l2CoefficientMap (certificateCoefficient 263)) = 8 := by
  decide +kernel
private theorem certificate_264 : HammingWeight (l2CoefficientMap (certificateCoefficient 264)) = 4 := by
  decide +kernel
private theorem certificate_265 : HammingWeight (l2CoefficientMap (certificateCoefficient 265)) = 8 := by
  decide +kernel
private theorem certificate_266 : HammingWeight (l2CoefficientMap (certificateCoefficient 266)) = 12 := by
  decide +kernel
private theorem certificate_267 : HammingWeight (l2CoefficientMap (certificateCoefficient 267)) = 8 := by
  decide +kernel
private theorem certificate_268 : HammingWeight (l2CoefficientMap (certificateCoefficient 268)) = 8 := by
  decide +kernel
private theorem certificate_269 : HammingWeight (l2CoefficientMap (certificateCoefficient 269)) = 8 := by
  decide +kernel
private theorem certificate_270 : HammingWeight (l2CoefficientMap (certificateCoefficient 270)) = 8 := by
  decide +kernel
private theorem certificate_271 : HammingWeight (l2CoefficientMap (certificateCoefficient 271)) = 8 := by
  decide +kernel
private theorem certificate_272 : HammingWeight (l2CoefficientMap (certificateCoefficient 272)) = 4 := by
  decide +kernel
private theorem certificate_273 : HammingWeight (l2CoefficientMap (certificateCoefficient 273)) = 8 := by
  decide +kernel
private theorem certificate_274 : HammingWeight (l2CoefficientMap (certificateCoefficient 274)) = 4 := by
  decide +kernel
private theorem certificate_275 : HammingWeight (l2CoefficientMap (certificateCoefficient 275)) = 8 := by
  decide +kernel
private theorem certificate_276 : HammingWeight (l2CoefficientMap (certificateCoefficient 276)) = 8 := by
  decide +kernel
private theorem certificate_277 : HammingWeight (l2CoefficientMap (certificateCoefficient 277)) = 8 := by
  decide +kernel
private theorem certificate_278 : HammingWeight (l2CoefficientMap (certificateCoefficient 278)) = 8 := by
  decide +kernel
private theorem certificate_279 : HammingWeight (l2CoefficientMap (certificateCoefficient 279)) = 8 := by
  decide +kernel
private theorem certificate_280 : HammingWeight (l2CoefficientMap (certificateCoefficient 280)) = 8 := by
  decide +kernel
private theorem certificate_281 : HammingWeight (l2CoefficientMap (certificateCoefficient 281)) = 4 := by
  decide +kernel
private theorem certificate_282 : HammingWeight (l2CoefficientMap (certificateCoefficient 282)) = 8 := by
  decide +kernel
private theorem certificate_283 : HammingWeight (l2CoefficientMap (certificateCoefficient 283)) = 12 := by
  decide +kernel
private theorem certificate_284 : HammingWeight (l2CoefficientMap (certificateCoefficient 284)) = 8 := by
  decide +kernel
private theorem certificate_285 : HammingWeight (l2CoefficientMap (certificateCoefficient 285)) = 8 := by
  decide +kernel
private theorem certificate_286 : HammingWeight (l2CoefficientMap (certificateCoefficient 286)) = 8 := by
  decide +kernel
private theorem certificate_287 : HammingWeight (l2CoefficientMap (certificateCoefficient 287)) = 8 := by
  decide +kernel
private theorem certificate_288 : HammingWeight (l2CoefficientMap (certificateCoefficient 288)) = 6 := by
  decide +kernel
private theorem certificate_289 : HammingWeight (l2CoefficientMap (certificateCoefficient 289)) = 6 := by
  decide +kernel
private theorem certificate_290 : HammingWeight (l2CoefficientMap (certificateCoefficient 290)) = 6 := by
  decide +kernel
private theorem certificate_291 : HammingWeight (l2CoefficientMap (certificateCoefficient 291)) = 6 := by
  decide +kernel
private theorem certificate_292 : HammingWeight (l2CoefficientMap (certificateCoefficient 292)) = 6 := by
  decide +kernel
private theorem certificate_293 : HammingWeight (l2CoefficientMap (certificateCoefficient 293)) = 10 := by
  decide +kernel
private theorem certificate_294 : HammingWeight (l2CoefficientMap (certificateCoefficient 294)) = 6 := by
  decide +kernel
private theorem certificate_295 : HammingWeight (l2CoefficientMap (certificateCoefficient 295)) = 10 := by
  decide +kernel
private theorem certificate_296 : HammingWeight (l2CoefficientMap (certificateCoefficient 296)) = 6 := by
  decide +kernel
private theorem certificate_297 : HammingWeight (l2CoefficientMap (certificateCoefficient 297)) = 6 := by
  decide +kernel
private theorem certificate_298 : HammingWeight (l2CoefficientMap (certificateCoefficient 298)) = 10 := by
  decide +kernel
private theorem certificate_299 : HammingWeight (l2CoefficientMap (certificateCoefficient 299)) = 10 := by
  decide +kernel
private theorem certificate_300 : HammingWeight (l2CoefficientMap (certificateCoefficient 300)) = 6 := by
  decide +kernel
private theorem certificate_301 : HammingWeight (l2CoefficientMap (certificateCoefficient 301)) = 10 := by
  decide +kernel
private theorem certificate_302 : HammingWeight (l2CoefficientMap (certificateCoefficient 302)) = 10 := by
  decide +kernel
private theorem certificate_303 : HammingWeight (l2CoefficientMap (certificateCoefficient 303)) = 6 := by
  decide +kernel
private theorem certificate_304 : HammingWeight (l2CoefficientMap (certificateCoefficient 304)) = 6 := by
  decide +kernel
private theorem certificate_305 : HammingWeight (l2CoefficientMap (certificateCoefficient 305)) = 6 := by
  decide +kernel
private theorem certificate_306 : HammingWeight (l2CoefficientMap (certificateCoefficient 306)) = 6 := by
  decide +kernel
private theorem certificate_307 : HammingWeight (l2CoefficientMap (certificateCoefficient 307)) = 6 := by
  decide +kernel
private theorem certificate_308 : HammingWeight (l2CoefficientMap (certificateCoefficient 308)) = 6 := by
  decide +kernel
private theorem certificate_309 : HammingWeight (l2CoefficientMap (certificateCoefficient 309)) = 10 := by
  decide +kernel
private theorem certificate_310 : HammingWeight (l2CoefficientMap (certificateCoefficient 310)) = 6 := by
  decide +kernel
private theorem certificate_311 : HammingWeight (l2CoefficientMap (certificateCoefficient 311)) = 10 := by
  decide +kernel
private theorem certificate_312 : HammingWeight (l2CoefficientMap (certificateCoefficient 312)) = 6 := by
  decide +kernel
private theorem certificate_313 : HammingWeight (l2CoefficientMap (certificateCoefficient 313)) = 6 := by
  decide +kernel
private theorem certificate_314 : HammingWeight (l2CoefficientMap (certificateCoefficient 314)) = 10 := by
  decide +kernel
private theorem certificate_315 : HammingWeight (l2CoefficientMap (certificateCoefficient 315)) = 10 := by
  decide +kernel
private theorem certificate_316 : HammingWeight (l2CoefficientMap (certificateCoefficient 316)) = 10 := by
  decide +kernel
private theorem certificate_317 : HammingWeight (l2CoefficientMap (certificateCoefficient 317)) = 6 := by
  decide +kernel
private theorem certificate_318 : HammingWeight (l2CoefficientMap (certificateCoefficient 318)) = 6 := by
  decide +kernel
private theorem certificate_319 : HammingWeight (l2CoefficientMap (certificateCoefficient 319)) = 10 := by
  decide +kernel
theorem word_table_block_4 (j : Fin 64) : HammingWeight (l2CoefficientMap (certificateCoefficient (4 * 64 + j.val))) = certificateWeightBlock 4 j := by
  change HammingWeight (l2CoefficientMap (certificateCoefficient (4 * 64 + j.val))) = (![4, 8, 4, 8, 8, 8, 8, 8, 4, 8, 12, 8, 8, 8, 8, 8, 4, 8, 4, 8, 8, 8, 8, 8, 8, 4, 8, 12, 8, 8, 8, 8, 6, 6, 6, 6, 6, 10, 6, 10, 6, 6, 10, 10, 6, 10, 10, 6, 6, 6, 6, 6, 6, 10, 6, 10, 6, 6, 10, 10, 10, 6, 6, 10] : Fin 64 → Nat) j
  fin_cases j
  · exact certificate_256
  · exact certificate_257
  · exact certificate_258
  · exact certificate_259
  · exact certificate_260
  · exact certificate_261
  · exact certificate_262
  · exact certificate_263
  · exact certificate_264
  · exact certificate_265
  · exact certificate_266
  · exact certificate_267
  · exact certificate_268
  · exact certificate_269
  · exact certificate_270
  · exact certificate_271
  · exact certificate_272
  · exact certificate_273
  · exact certificate_274
  · exact certificate_275
  · exact certificate_276
  · exact certificate_277
  · exact certificate_278
  · exact certificate_279
  · exact certificate_280
  · exact certificate_281
  · exact certificate_282
  · exact certificate_283
  · exact certificate_284
  · exact certificate_285
  · exact certificate_286
  · exact certificate_287
  · exact certificate_288
  · exact certificate_289
  · exact certificate_290
  · exact certificate_291
  · exact certificate_292
  · exact certificate_293
  · exact certificate_294
  · exact certificate_295
  · exact certificate_296
  · exact certificate_297
  · exact certificate_298
  · exact certificate_299
  · exact certificate_300
  · exact certificate_301
  · exact certificate_302
  · exact certificate_303
  · exact certificate_304
  · exact certificate_305
  · exact certificate_306
  · exact certificate_307
  · exact certificate_308
  · exact certificate_309
  · exact certificate_310
  · exact certificate_311
  · exact certificate_312
  · exact certificate_313
  · exact certificate_314
  · exact certificate_315
  · exact certificate_316
  · exact certificate_317
  · exact certificate_318
  · exact certificate_319


end QEC.Distillation.BK15.CertifiedWeights


