-- Prove2me | Definitions.Def_QECert_FifteenWeights_WeightChunk6
-- name    : QECert_FifteenWeights_WeightChunk6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:56:53.852654+00:00
-- url     : https://prove2.me/theorems/2b5c08e4-07c9-437d-bf3b-fe4df51e3207
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
private theorem certificate_384 : HammingWeight (l2CoefficientMap (certificateCoefficient 384)) = 4 := by
  decide +kernel
private theorem certificate_385 : HammingWeight (l2CoefficientMap (certificateCoefficient 385)) = 8 := by
  decide +kernel
private theorem certificate_386 : HammingWeight (l2CoefficientMap (certificateCoefficient 386)) = 4 := by
  decide +kernel
private theorem certificate_387 : HammingWeight (l2CoefficientMap (certificateCoefficient 387)) = 8 := by
  decide +kernel
private theorem certificate_388 : HammingWeight (l2CoefficientMap (certificateCoefficient 388)) = 8 := by
  decide +kernel
private theorem certificate_389 : HammingWeight (l2CoefficientMap (certificateCoefficient 389)) = 8 := by
  decide +kernel
private theorem certificate_390 : HammingWeight (l2CoefficientMap (certificateCoefficient 390)) = 8 := by
  decide +kernel
private theorem certificate_391 : HammingWeight (l2CoefficientMap (certificateCoefficient 391)) = 8 := by
  decide +kernel
private theorem certificate_392 : HammingWeight (l2CoefficientMap (certificateCoefficient 392)) = 8 := by
  decide +kernel
private theorem certificate_393 : HammingWeight (l2CoefficientMap (certificateCoefficient 393)) = 8 := by
  decide +kernel
private theorem certificate_394 : HammingWeight (l2CoefficientMap (certificateCoefficient 394)) = 8 := by
  decide +kernel
private theorem certificate_395 : HammingWeight (l2CoefficientMap (certificateCoefficient 395)) = 8 := by
  decide +kernel
private theorem certificate_396 : HammingWeight (l2CoefficientMap (certificateCoefficient 396)) = 4 := by
  decide +kernel
private theorem certificate_397 : HammingWeight (l2CoefficientMap (certificateCoefficient 397)) = 8 := by
  decide +kernel
private theorem certificate_398 : HammingWeight (l2CoefficientMap (certificateCoefficient 398)) = 12 := by
  decide +kernel
private theorem certificate_399 : HammingWeight (l2CoefficientMap (certificateCoefficient 399)) = 8 := by
  decide +kernel
private theorem certificate_400 : HammingWeight (l2CoefficientMap (certificateCoefficient 400)) = 4 := by
  decide +kernel
private theorem certificate_401 : HammingWeight (l2CoefficientMap (certificateCoefficient 401)) = 8 := by
  decide +kernel
private theorem certificate_402 : HammingWeight (l2CoefficientMap (certificateCoefficient 402)) = 4 := by
  decide +kernel
private theorem certificate_403 : HammingWeight (l2CoefficientMap (certificateCoefficient 403)) = 8 := by
  decide +kernel
private theorem certificate_404 : HammingWeight (l2CoefficientMap (certificateCoefficient 404)) = 8 := by
  decide +kernel
private theorem certificate_405 : HammingWeight (l2CoefficientMap (certificateCoefficient 405)) = 8 := by
  decide +kernel
private theorem certificate_406 : HammingWeight (l2CoefficientMap (certificateCoefficient 406)) = 8 := by
  decide +kernel
private theorem certificate_407 : HammingWeight (l2CoefficientMap (certificateCoefficient 407)) = 8 := by
  decide +kernel
private theorem certificate_408 : HammingWeight (l2CoefficientMap (certificateCoefficient 408)) = 8 := by
  decide +kernel
private theorem certificate_409 : HammingWeight (l2CoefficientMap (certificateCoefficient 409)) = 8 := by
  decide +kernel
private theorem certificate_410 : HammingWeight (l2CoefficientMap (certificateCoefficient 410)) = 8 := by
  decide +kernel
private theorem certificate_411 : HammingWeight (l2CoefficientMap (certificateCoefficient 411)) = 8 := by
  decide +kernel
private theorem certificate_412 : HammingWeight (l2CoefficientMap (certificateCoefficient 412)) = 8 := by
  decide +kernel
private theorem certificate_413 : HammingWeight (l2CoefficientMap (certificateCoefficient 413)) = 4 := by
  decide +kernel
private theorem certificate_414 : HammingWeight (l2CoefficientMap (certificateCoefficient 414)) = 8 := by
  decide +kernel
private theorem certificate_415 : HammingWeight (l2CoefficientMap (certificateCoefficient 415)) = 12 := by
  decide +kernel
private theorem certificate_416 : HammingWeight (l2CoefficientMap (certificateCoefficient 416)) = 6 := by
  decide +kernel
private theorem certificate_417 : HammingWeight (l2CoefficientMap (certificateCoefficient 417)) = 6 := by
  decide +kernel
private theorem certificate_418 : HammingWeight (l2CoefficientMap (certificateCoefficient 418)) = 6 := by
  decide +kernel
private theorem certificate_419 : HammingWeight (l2CoefficientMap (certificateCoefficient 419)) = 6 := by
  decide +kernel
private theorem certificate_420 : HammingWeight (l2CoefficientMap (certificateCoefficient 420)) = 6 := by
  decide +kernel
private theorem certificate_421 : HammingWeight (l2CoefficientMap (certificateCoefficient 421)) = 10 := by
  decide +kernel
private theorem certificate_422 : HammingWeight (l2CoefficientMap (certificateCoefficient 422)) = 6 := by
  decide +kernel
private theorem certificate_423 : HammingWeight (l2CoefficientMap (certificateCoefficient 423)) = 10 := by
  decide +kernel
private theorem certificate_424 : HammingWeight (l2CoefficientMap (certificateCoefficient 424)) = 6 := by
  decide +kernel
private theorem certificate_425 : HammingWeight (l2CoefficientMap (certificateCoefficient 425)) = 10 := by
  decide +kernel
private theorem certificate_426 : HammingWeight (l2CoefficientMap (certificateCoefficient 426)) = 10 := by
  decide +kernel
private theorem certificate_427 : HammingWeight (l2CoefficientMap (certificateCoefficient 427)) = 6 := by
  decide +kernel
private theorem certificate_428 : HammingWeight (l2CoefficientMap (certificateCoefficient 428)) = 6 := by
  decide +kernel
private theorem certificate_429 : HammingWeight (l2CoefficientMap (certificateCoefficient 429)) = 6 := by
  decide +kernel
private theorem certificate_430 : HammingWeight (l2CoefficientMap (certificateCoefficient 430)) = 10 := by
  decide +kernel
private theorem certificate_431 : HammingWeight (l2CoefficientMap (certificateCoefficient 431)) = 10 := by
  decide +kernel
private theorem certificate_432 : HammingWeight (l2CoefficientMap (certificateCoefficient 432)) = 6 := by
  decide +kernel
private theorem certificate_433 : HammingWeight (l2CoefficientMap (certificateCoefficient 433)) = 6 := by
  decide +kernel
private theorem certificate_434 : HammingWeight (l2CoefficientMap (certificateCoefficient 434)) = 6 := by
  decide +kernel
private theorem certificate_435 : HammingWeight (l2CoefficientMap (certificateCoefficient 435)) = 6 := by
  decide +kernel
private theorem certificate_436 : HammingWeight (l2CoefficientMap (certificateCoefficient 436)) = 6 := by
  decide +kernel
private theorem certificate_437 : HammingWeight (l2CoefficientMap (certificateCoefficient 437)) = 10 := by
  decide +kernel
private theorem certificate_438 : HammingWeight (l2CoefficientMap (certificateCoefficient 438)) = 6 := by
  decide +kernel
private theorem certificate_439 : HammingWeight (l2CoefficientMap (certificateCoefficient 439)) = 10 := by
  decide +kernel
private theorem certificate_440 : HammingWeight (l2CoefficientMap (certificateCoefficient 440)) = 10 := by
  decide +kernel
private theorem certificate_441 : HammingWeight (l2CoefficientMap (certificateCoefficient 441)) = 6 := by
  decide +kernel
private theorem certificate_442 : HammingWeight (l2CoefficientMap (certificateCoefficient 442)) = 6 := by
  decide +kernel
private theorem certificate_443 : HammingWeight (l2CoefficientMap (certificateCoefficient 443)) = 10 := by
  decide +kernel
private theorem certificate_444 : HammingWeight (l2CoefficientMap (certificateCoefficient 444)) = 6 := by
  decide +kernel
private theorem certificate_445 : HammingWeight (l2CoefficientMap (certificateCoefficient 445)) = 6 := by
  decide +kernel
private theorem certificate_446 : HammingWeight (l2CoefficientMap (certificateCoefficient 446)) = 10 := by
  decide +kernel
private theorem certificate_447 : HammingWeight (l2CoefficientMap (certificateCoefficient 447)) = 10 := by
  decide +kernel
theorem word_table_block_6 (j : Fin 64) : HammingWeight (l2CoefficientMap (certificateCoefficient (6 * 64 + j.val))) = certificateWeightBlock 6 j := by
  change HammingWeight (l2CoefficientMap (certificateCoefficient (6 * 64 + j.val))) = (![4, 8, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 8, 12, 8, 4, 8, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 8, 12, 6, 6, 6, 6, 6, 10, 6, 10, 6, 10, 10, 6, 6, 6, 10, 10, 6, 6, 6, 6, 6, 10, 6, 10, 10, 6, 6, 10, 6, 6, 10, 10] : Fin 64 → Nat) j
  fin_cases j
  · exact certificate_384
  · exact certificate_385
  · exact certificate_386
  · exact certificate_387
  · exact certificate_388
  · exact certificate_389
  · exact certificate_390
  · exact certificate_391
  · exact certificate_392
  · exact certificate_393
  · exact certificate_394
  · exact certificate_395
  · exact certificate_396
  · exact certificate_397
  · exact certificate_398
  · exact certificate_399
  · exact certificate_400
  · exact certificate_401
  · exact certificate_402
  · exact certificate_403
  · exact certificate_404
  · exact certificate_405
  · exact certificate_406
  · exact certificate_407
  · exact certificate_408
  · exact certificate_409
  · exact certificate_410
  · exact certificate_411
  · exact certificate_412
  · exact certificate_413
  · exact certificate_414
  · exact certificate_415
  · exact certificate_416
  · exact certificate_417
  · exact certificate_418
  · exact certificate_419
  · exact certificate_420
  · exact certificate_421
  · exact certificate_422
  · exact certificate_423
  · exact certificate_424
  · exact certificate_425
  · exact certificate_426
  · exact certificate_427
  · exact certificate_428
  · exact certificate_429
  · exact certificate_430
  · exact certificate_431
  · exact certificate_432
  · exact certificate_433
  · exact certificate_434
  · exact certificate_435
  · exact certificate_436
  · exact certificate_437
  · exact certificate_438
  · exact certificate_439
  · exact certificate_440
  · exact certificate_441
  · exact certificate_442
  · exact certificate_443
  · exact certificate_444
  · exact certificate_445
  · exact certificate_446
  · exact certificate_447


end QEC.Distillation.BK15.CertifiedWeights


