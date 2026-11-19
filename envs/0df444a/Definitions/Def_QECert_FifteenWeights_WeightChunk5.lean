-- Prove2me | Definitions.Def_QECert_FifteenWeights_WeightChunk5
-- name    : QECert_FifteenWeights_WeightChunk5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:57:14.547324+00:00
-- url     : https://prove2.me/theorems/36932148-0bb3-4091-bc25-a5a92e3c1251
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
private theorem certificate_320 : HammingWeight (l2CoefficientMap (certificateCoefficient 320)) = 4 := by
  decide +kernel
private theorem certificate_321 : HammingWeight (l2CoefficientMap (certificateCoefficient 321)) = 8 := by
  decide +kernel
private theorem certificate_322 : HammingWeight (l2CoefficientMap (certificateCoefficient 322)) = 8 := by
  decide +kernel
private theorem certificate_323 : HammingWeight (l2CoefficientMap (certificateCoefficient 323)) = 4 := by
  decide +kernel
private theorem certificate_324 : HammingWeight (l2CoefficientMap (certificateCoefficient 324)) = 8 := by
  decide +kernel
private theorem certificate_325 : HammingWeight (l2CoefficientMap (certificateCoefficient 325)) = 8 := by
  decide +kernel
private theorem certificate_326 : HammingWeight (l2CoefficientMap (certificateCoefficient 326)) = 8 := by
  decide +kernel
private theorem certificate_327 : HammingWeight (l2CoefficientMap (certificateCoefficient 327)) = 8 := by
  decide +kernel
private theorem certificate_328 : HammingWeight (l2CoefficientMap (certificateCoefficient 328)) = 4 := by
  decide +kernel
private theorem certificate_329 : HammingWeight (l2CoefficientMap (certificateCoefficient 329)) = 8 := by
  decide +kernel
private theorem certificate_330 : HammingWeight (l2CoefficientMap (certificateCoefficient 330)) = 8 := by
  decide +kernel
private theorem certificate_331 : HammingWeight (l2CoefficientMap (certificateCoefficient 331)) = 12 := by
  decide +kernel
private theorem certificate_332 : HammingWeight (l2CoefficientMap (certificateCoefficient 332)) = 8 := by
  decide +kernel
private theorem certificate_333 : HammingWeight (l2CoefficientMap (certificateCoefficient 333)) = 8 := by
  decide +kernel
private theorem certificate_334 : HammingWeight (l2CoefficientMap (certificateCoefficient 334)) = 8 := by
  decide +kernel
private theorem certificate_335 : HammingWeight (l2CoefficientMap (certificateCoefficient 335)) = 8 := by
  decide +kernel
private theorem certificate_336 : HammingWeight (l2CoefficientMap (certificateCoefficient 336)) = 8 := by
  decide +kernel
private theorem certificate_337 : HammingWeight (l2CoefficientMap (certificateCoefficient 337)) = 4 := by
  decide +kernel
private theorem certificate_338 : HammingWeight (l2CoefficientMap (certificateCoefficient 338)) = 4 := by
  decide +kernel
private theorem certificate_339 : HammingWeight (l2CoefficientMap (certificateCoefficient 339)) = 8 := by
  decide +kernel
private theorem certificate_340 : HammingWeight (l2CoefficientMap (certificateCoefficient 340)) = 8 := by
  decide +kernel
private theorem certificate_341 : HammingWeight (l2CoefficientMap (certificateCoefficient 341)) = 8 := by
  decide +kernel
private theorem certificate_342 : HammingWeight (l2CoefficientMap (certificateCoefficient 342)) = 8 := by
  decide +kernel
private theorem certificate_343 : HammingWeight (l2CoefficientMap (certificateCoefficient 343)) = 8 := by
  decide +kernel
private theorem certificate_344 : HammingWeight (l2CoefficientMap (certificateCoefficient 344)) = 4 := by
  decide +kernel
private theorem certificate_345 : HammingWeight (l2CoefficientMap (certificateCoefficient 345)) = 8 := by
  decide +kernel
private theorem certificate_346 : HammingWeight (l2CoefficientMap (certificateCoefficient 346)) = 8 := by
  decide +kernel
private theorem certificate_347 : HammingWeight (l2CoefficientMap (certificateCoefficient 347)) = 12 := by
  decide +kernel
private theorem certificate_348 : HammingWeight (l2CoefficientMap (certificateCoefficient 348)) = 8 := by
  decide +kernel
private theorem certificate_349 : HammingWeight (l2CoefficientMap (certificateCoefficient 349)) = 8 := by
  decide +kernel
private theorem certificate_350 : HammingWeight (l2CoefficientMap (certificateCoefficient 350)) = 8 := by
  decide +kernel
private theorem certificate_351 : HammingWeight (l2CoefficientMap (certificateCoefficient 351)) = 8 := by
  decide +kernel
private theorem certificate_352 : HammingWeight (l2CoefficientMap (certificateCoefficient 352)) = 6 := by
  decide +kernel
private theorem certificate_353 : HammingWeight (l2CoefficientMap (certificateCoefficient 353)) = 6 := by
  decide +kernel
private theorem certificate_354 : HammingWeight (l2CoefficientMap (certificateCoefficient 354)) = 6 := by
  decide +kernel
private theorem certificate_355 : HammingWeight (l2CoefficientMap (certificateCoefficient 355)) = 6 := by
  decide +kernel
private theorem certificate_356 : HammingWeight (l2CoefficientMap (certificateCoefficient 356)) = 6 := by
  decide +kernel
private theorem certificate_357 : HammingWeight (l2CoefficientMap (certificateCoefficient 357)) = 10 := by
  decide +kernel
private theorem certificate_358 : HammingWeight (l2CoefficientMap (certificateCoefficient 358)) = 10 := by
  decide +kernel
private theorem certificate_359 : HammingWeight (l2CoefficientMap (certificateCoefficient 359)) = 6 := by
  decide +kernel
private theorem certificate_360 : HammingWeight (l2CoefficientMap (certificateCoefficient 360)) = 6 := by
  decide +kernel
private theorem certificate_361 : HammingWeight (l2CoefficientMap (certificateCoefficient 361)) = 6 := by
  decide +kernel
private theorem certificate_362 : HammingWeight (l2CoefficientMap (certificateCoefficient 362)) = 10 := by
  decide +kernel
private theorem certificate_363 : HammingWeight (l2CoefficientMap (certificateCoefficient 363)) = 10 := by
  decide +kernel
private theorem certificate_364 : HammingWeight (l2CoefficientMap (certificateCoefficient 364)) = 6 := by
  decide +kernel
private theorem certificate_365 : HammingWeight (l2CoefficientMap (certificateCoefficient 365)) = 10 := by
  decide +kernel
private theorem certificate_366 : HammingWeight (l2CoefficientMap (certificateCoefficient 366)) = 6 := by
  decide +kernel
private theorem certificate_367 : HammingWeight (l2CoefficientMap (certificateCoefficient 367)) = 10 := by
  decide +kernel
private theorem certificate_368 : HammingWeight (l2CoefficientMap (certificateCoefficient 368)) = 6 := by
  decide +kernel
private theorem certificate_369 : HammingWeight (l2CoefficientMap (certificateCoefficient 369)) = 6 := by
  decide +kernel
private theorem certificate_370 : HammingWeight (l2CoefficientMap (certificateCoefficient 370)) = 6 := by
  decide +kernel
private theorem certificate_371 : HammingWeight (l2CoefficientMap (certificateCoefficient 371)) = 6 := by
  decide +kernel
private theorem certificate_372 : HammingWeight (l2CoefficientMap (certificateCoefficient 372)) = 10 := by
  decide +kernel
private theorem certificate_373 : HammingWeight (l2CoefficientMap (certificateCoefficient 373)) = 6 := by
  decide +kernel
private theorem certificate_374 : HammingWeight (l2CoefficientMap (certificateCoefficient 374)) = 6 := by
  decide +kernel
private theorem certificate_375 : HammingWeight (l2CoefficientMap (certificateCoefficient 375)) = 10 := by
  decide +kernel
private theorem certificate_376 : HammingWeight (l2CoefficientMap (certificateCoefficient 376)) = 6 := by
  decide +kernel
private theorem certificate_377 : HammingWeight (l2CoefficientMap (certificateCoefficient 377)) = 6 := by
  decide +kernel
private theorem certificate_378 : HammingWeight (l2CoefficientMap (certificateCoefficient 378)) = 10 := by
  decide +kernel
private theorem certificate_379 : HammingWeight (l2CoefficientMap (certificateCoefficient 379)) = 10 := by
  decide +kernel
private theorem certificate_380 : HammingWeight (l2CoefficientMap (certificateCoefficient 380)) = 6 := by
  decide +kernel
private theorem certificate_381 : HammingWeight (l2CoefficientMap (certificateCoefficient 381)) = 10 := by
  decide +kernel
private theorem certificate_382 : HammingWeight (l2CoefficientMap (certificateCoefficient 382)) = 6 := by
  decide +kernel
private theorem certificate_383 : HammingWeight (l2CoefficientMap (certificateCoefficient 383)) = 10 := by
  decide +kernel
theorem word_table_block_5 (j : Fin 64) : HammingWeight (l2CoefficientMap (certificateCoefficient (5 * 64 + j.val))) = certificateWeightBlock 5 j := by
  change HammingWeight (l2CoefficientMap (certificateCoefficient (5 * 64 + j.val))) = (![4, 8, 8, 4, 8, 8, 8, 8, 4, 8, 8, 12, 8, 8, 8, 8, 8, 4, 4, 8, 8, 8, 8, 8, 4, 8, 8, 12, 8, 8, 8, 8, 6, 6, 6, 6, 6, 10, 10, 6, 6, 6, 10, 10, 6, 10, 6, 10, 6, 6, 6, 6, 10, 6, 6, 10, 6, 6, 10, 10, 6, 10, 6, 10] : Fin 64 → Nat) j
  fin_cases j
  · exact certificate_320
  · exact certificate_321
  · exact certificate_322
  · exact certificate_323
  · exact certificate_324
  · exact certificate_325
  · exact certificate_326
  · exact certificate_327
  · exact certificate_328
  · exact certificate_329
  · exact certificate_330
  · exact certificate_331
  · exact certificate_332
  · exact certificate_333
  · exact certificate_334
  · exact certificate_335
  · exact certificate_336
  · exact certificate_337
  · exact certificate_338
  · exact certificate_339
  · exact certificate_340
  · exact certificate_341
  · exact certificate_342
  · exact certificate_343
  · exact certificate_344
  · exact certificate_345
  · exact certificate_346
  · exact certificate_347
  · exact certificate_348
  · exact certificate_349
  · exact certificate_350
  · exact certificate_351
  · exact certificate_352
  · exact certificate_353
  · exact certificate_354
  · exact certificate_355
  · exact certificate_356
  · exact certificate_357
  · exact certificate_358
  · exact certificate_359
  · exact certificate_360
  · exact certificate_361
  · exact certificate_362
  · exact certificate_363
  · exact certificate_364
  · exact certificate_365
  · exact certificate_366
  · exact certificate_367
  · exact certificate_368
  · exact certificate_369
  · exact certificate_370
  · exact certificate_371
  · exact certificate_372
  · exact certificate_373
  · exact certificate_374
  · exact certificate_375
  · exact certificate_376
  · exact certificate_377
  · exact certificate_378
  · exact certificate_379
  · exact certificate_380
  · exact certificate_381
  · exact certificate_382
  · exact certificate_383


end QEC.Distillation.BK15.CertifiedWeights


