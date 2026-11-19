-- Prove2me | Definitions.Def_QECert_FifteenWeights_WeightChunk7
-- name    : QECert_FifteenWeights_WeightChunk7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:57:03.976525+00:00
-- url     : https://prove2.me/theorems/feddf1e0-614b-4421-811b-adde9164ee93
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
private theorem certificate_448 : HammingWeight (l2CoefficientMap (certificateCoefficient 448)) = 6 := by
  decide +kernel
private theorem certificate_449 : HammingWeight (l2CoefficientMap (certificateCoefficient 449)) = 6 := by
  decide +kernel
private theorem certificate_450 : HammingWeight (l2CoefficientMap (certificateCoefficient 450)) = 6 := by
  decide +kernel
private theorem certificate_451 : HammingWeight (l2CoefficientMap (certificateCoefficient 451)) = 6 := by
  decide +kernel
private theorem certificate_452 : HammingWeight (l2CoefficientMap (certificateCoefficient 452)) = 6 := by
  decide +kernel
private theorem certificate_453 : HammingWeight (l2CoefficientMap (certificateCoefficient 453)) = 10 := by
  decide +kernel
private theorem certificate_454 : HammingWeight (l2CoefficientMap (certificateCoefficient 454)) = 10 := by
  decide +kernel
private theorem certificate_455 : HammingWeight (l2CoefficientMap (certificateCoefficient 455)) = 6 := by
  decide +kernel
private theorem certificate_456 : HammingWeight (l2CoefficientMap (certificateCoefficient 456)) = 6 := by
  decide +kernel
private theorem certificate_457 : HammingWeight (l2CoefficientMap (certificateCoefficient 457)) = 10 := by
  decide +kernel
private theorem certificate_458 : HammingWeight (l2CoefficientMap (certificateCoefficient 458)) = 6 := by
  decide +kernel
private theorem certificate_459 : HammingWeight (l2CoefficientMap (certificateCoefficient 459)) = 10 := by
  decide +kernel
private theorem certificate_460 : HammingWeight (l2CoefficientMap (certificateCoefficient 460)) = 6 := by
  decide +kernel
private theorem certificate_461 : HammingWeight (l2CoefficientMap (certificateCoefficient 461)) = 6 := by
  decide +kernel
private theorem certificate_462 : HammingWeight (l2CoefficientMap (certificateCoefficient 462)) = 10 := by
  decide +kernel
private theorem certificate_463 : HammingWeight (l2CoefficientMap (certificateCoefficient 463)) = 10 := by
  decide +kernel
private theorem certificate_464 : HammingWeight (l2CoefficientMap (certificateCoefficient 464)) = 6 := by
  decide +kernel
private theorem certificate_465 : HammingWeight (l2CoefficientMap (certificateCoefficient 465)) = 6 := by
  decide +kernel
private theorem certificate_466 : HammingWeight (l2CoefficientMap (certificateCoefficient 466)) = 6 := by
  decide +kernel
private theorem certificate_467 : HammingWeight (l2CoefficientMap (certificateCoefficient 467)) = 6 := by
  decide +kernel
private theorem certificate_468 : HammingWeight (l2CoefficientMap (certificateCoefficient 468)) = 10 := by
  decide +kernel
private theorem certificate_469 : HammingWeight (l2CoefficientMap (certificateCoefficient 469)) = 6 := by
  decide +kernel
private theorem certificate_470 : HammingWeight (l2CoefficientMap (certificateCoefficient 470)) = 6 := by
  decide +kernel
private theorem certificate_471 : HammingWeight (l2CoefficientMap (certificateCoefficient 471)) = 10 := by
  decide +kernel
private theorem certificate_472 : HammingWeight (l2CoefficientMap (certificateCoefficient 472)) = 6 := by
  decide +kernel
private theorem certificate_473 : HammingWeight (l2CoefficientMap (certificateCoefficient 473)) = 10 := by
  decide +kernel
private theorem certificate_474 : HammingWeight (l2CoefficientMap (certificateCoefficient 474)) = 6 := by
  decide +kernel
private theorem certificate_475 : HammingWeight (l2CoefficientMap (certificateCoefficient 475)) = 10 := by
  decide +kernel
private theorem certificate_476 : HammingWeight (l2CoefficientMap (certificateCoefficient 476)) = 6 := by
  decide +kernel
private theorem certificate_477 : HammingWeight (l2CoefficientMap (certificateCoefficient 477)) = 6 := by
  decide +kernel
private theorem certificate_478 : HammingWeight (l2CoefficientMap (certificateCoefficient 478)) = 10 := by
  decide +kernel
private theorem certificate_479 : HammingWeight (l2CoefficientMap (certificateCoefficient 479)) = 10 := by
  decide +kernel
private theorem certificate_480 : HammingWeight (l2CoefficientMap (certificateCoefficient 480)) = 4 := by
  decide +kernel
private theorem certificate_481 : HammingWeight (l2CoefficientMap (certificateCoefficient 481)) = 8 := by
  decide +kernel
private theorem certificate_482 : HammingWeight (l2CoefficientMap (certificateCoefficient 482)) = 8 := by
  decide +kernel
private theorem certificate_483 : HammingWeight (l2CoefficientMap (certificateCoefficient 483)) = 4 := by
  decide +kernel
private theorem certificate_484 : HammingWeight (l2CoefficientMap (certificateCoefficient 484)) = 8 := by
  decide +kernel
private theorem certificate_485 : HammingWeight (l2CoefficientMap (certificateCoefficient 485)) = 8 := by
  decide +kernel
private theorem certificate_486 : HammingWeight (l2CoefficientMap (certificateCoefficient 486)) = 8 := by
  decide +kernel
private theorem certificate_487 : HammingWeight (l2CoefficientMap (certificateCoefficient 487)) = 8 := by
  decide +kernel
private theorem certificate_488 : HammingWeight (l2CoefficientMap (certificateCoefficient 488)) = 8 := by
  decide +kernel
private theorem certificate_489 : HammingWeight (l2CoefficientMap (certificateCoefficient 489)) = 8 := by
  decide +kernel
private theorem certificate_490 : HammingWeight (l2CoefficientMap (certificateCoefficient 490)) = 8 := by
  decide +kernel
private theorem certificate_491 : HammingWeight (l2CoefficientMap (certificateCoefficient 491)) = 8 := by
  decide +kernel
private theorem certificate_492 : HammingWeight (l2CoefficientMap (certificateCoefficient 492)) = 4 := by
  decide +kernel
private theorem certificate_493 : HammingWeight (l2CoefficientMap (certificateCoefficient 493)) = 8 := by
  decide +kernel
private theorem certificate_494 : HammingWeight (l2CoefficientMap (certificateCoefficient 494)) = 8 := by
  decide +kernel
private theorem certificate_495 : HammingWeight (l2CoefficientMap (certificateCoefficient 495)) = 12 := by
  decide +kernel
private theorem certificate_496 : HammingWeight (l2CoefficientMap (certificateCoefficient 496)) = 8 := by
  decide +kernel
private theorem certificate_497 : HammingWeight (l2CoefficientMap (certificateCoefficient 497)) = 4 := by
  decide +kernel
private theorem certificate_498 : HammingWeight (l2CoefficientMap (certificateCoefficient 498)) = 4 := by
  decide +kernel
private theorem certificate_499 : HammingWeight (l2CoefficientMap (certificateCoefficient 499)) = 8 := by
  decide +kernel
private theorem certificate_500 : HammingWeight (l2CoefficientMap (certificateCoefficient 500)) = 8 := by
  decide +kernel
private theorem certificate_501 : HammingWeight (l2CoefficientMap (certificateCoefficient 501)) = 8 := by
  decide +kernel
private theorem certificate_502 : HammingWeight (l2CoefficientMap (certificateCoefficient 502)) = 8 := by
  decide +kernel
private theorem certificate_503 : HammingWeight (l2CoefficientMap (certificateCoefficient 503)) = 8 := by
  decide +kernel
private theorem certificate_504 : HammingWeight (l2CoefficientMap (certificateCoefficient 504)) = 8 := by
  decide +kernel
private theorem certificate_505 : HammingWeight (l2CoefficientMap (certificateCoefficient 505)) = 8 := by
  decide +kernel
private theorem certificate_506 : HammingWeight (l2CoefficientMap (certificateCoefficient 506)) = 8 := by
  decide +kernel
private theorem certificate_507 : HammingWeight (l2CoefficientMap (certificateCoefficient 507)) = 8 := by
  decide +kernel
private theorem certificate_508 : HammingWeight (l2CoefficientMap (certificateCoefficient 508)) = 4 := by
  decide +kernel
private theorem certificate_509 : HammingWeight (l2CoefficientMap (certificateCoefficient 509)) = 8 := by
  decide +kernel
private theorem certificate_510 : HammingWeight (l2CoefficientMap (certificateCoefficient 510)) = 8 := by
  decide +kernel
private theorem certificate_511 : HammingWeight (l2CoefficientMap (certificateCoefficient 511)) = 12 := by
  decide +kernel
theorem word_table_block_7 (j : Fin 64) : HammingWeight (l2CoefficientMap (certificateCoefficient (7 * 64 + j.val))) = certificateWeightBlock 7 j := by
  change HammingWeight (l2CoefficientMap (certificateCoefficient (7 * 64 + j.val))) = (![6, 6, 6, 6, 6, 10, 10, 6, 6, 10, 6, 10, 6, 6, 10, 10, 6, 6, 6, 6, 10, 6, 6, 10, 6, 10, 6, 10, 6, 6, 10, 10, 4, 8, 8, 4, 8, 8, 8, 8, 8, 8, 8, 8, 4, 8, 8, 12, 8, 4, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 8, 8, 12] : Fin 64 → Nat) j
  fin_cases j
  · exact certificate_448
  · exact certificate_449
  · exact certificate_450
  · exact certificate_451
  · exact certificate_452
  · exact certificate_453
  · exact certificate_454
  · exact certificate_455
  · exact certificate_456
  · exact certificate_457
  · exact certificate_458
  · exact certificate_459
  · exact certificate_460
  · exact certificate_461
  · exact certificate_462
  · exact certificate_463
  · exact certificate_464
  · exact certificate_465
  · exact certificate_466
  · exact certificate_467
  · exact certificate_468
  · exact certificate_469
  · exact certificate_470
  · exact certificate_471
  · exact certificate_472
  · exact certificate_473
  · exact certificate_474
  · exact certificate_475
  · exact certificate_476
  · exact certificate_477
  · exact certificate_478
  · exact certificate_479
  · exact certificate_480
  · exact certificate_481
  · exact certificate_482
  · exact certificate_483
  · exact certificate_484
  · exact certificate_485
  · exact certificate_486
  · exact certificate_487
  · exact certificate_488
  · exact certificate_489
  · exact certificate_490
  · exact certificate_491
  · exact certificate_492
  · exact certificate_493
  · exact certificate_494
  · exact certificate_495
  · exact certificate_496
  · exact certificate_497
  · exact certificate_498
  · exact certificate_499
  · exact certificate_500
  · exact certificate_501
  · exact certificate_502
  · exact certificate_503
  · exact certificate_504
  · exact certificate_505
  · exact certificate_506
  · exact certificate_507
  · exact certificate_508
  · exact certificate_509
  · exact certificate_510
  · exact certificate_511


end QEC.Distillation.BK15.CertifiedWeights


