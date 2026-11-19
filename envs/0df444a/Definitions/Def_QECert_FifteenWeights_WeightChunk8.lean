-- Prove2me | Definitions.Def_QECert_FifteenWeights_WeightChunk8
-- name    : QECert_FifteenWeights_WeightChunk8
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:56:57.154204+00:00
-- url     : https://prove2.me/theorems/42daf7d8-7956-47c0-8da7-6ae023978ebb
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
private theorem certificate_512 : HammingWeight (l2CoefficientMap (certificateCoefficient 512)) = 4 := by
  decide +kernel
private theorem certificate_513 : HammingWeight (l2CoefficientMap (certificateCoefficient 513)) = 8 := by
  decide +kernel
private theorem certificate_514 : HammingWeight (l2CoefficientMap (certificateCoefficient 514)) = 8 := by
  decide +kernel
private theorem certificate_515 : HammingWeight (l2CoefficientMap (certificateCoefficient 515)) = 8 := by
  decide +kernel
private theorem certificate_516 : HammingWeight (l2CoefficientMap (certificateCoefficient 516)) = 4 := by
  decide +kernel
private theorem certificate_517 : HammingWeight (l2CoefficientMap (certificateCoefficient 517)) = 8 := by
  decide +kernel
private theorem certificate_518 : HammingWeight (l2CoefficientMap (certificateCoefficient 518)) = 8 := by
  decide +kernel
private theorem certificate_519 : HammingWeight (l2CoefficientMap (certificateCoefficient 519)) = 8 := by
  decide +kernel
private theorem certificate_520 : HammingWeight (l2CoefficientMap (certificateCoefficient 520)) = 4 := by
  decide +kernel
private theorem certificate_521 : HammingWeight (l2CoefficientMap (certificateCoefficient 521)) = 8 := by
  decide +kernel
private theorem certificate_522 : HammingWeight (l2CoefficientMap (certificateCoefficient 522)) = 8 := by
  decide +kernel
private theorem certificate_523 : HammingWeight (l2CoefficientMap (certificateCoefficient 523)) = 8 := by
  decide +kernel
private theorem certificate_524 : HammingWeight (l2CoefficientMap (certificateCoefficient 524)) = 12 := by
  decide +kernel
private theorem certificate_525 : HammingWeight (l2CoefficientMap (certificateCoefficient 525)) = 8 := by
  decide +kernel
private theorem certificate_526 : HammingWeight (l2CoefficientMap (certificateCoefficient 526)) = 8 := by
  decide +kernel
private theorem certificate_527 : HammingWeight (l2CoefficientMap (certificateCoefficient 527)) = 8 := by
  decide +kernel
private theorem certificate_528 : HammingWeight (l2CoefficientMap (certificateCoefficient 528)) = 6 := by
  decide +kernel
private theorem certificate_529 : HammingWeight (l2CoefficientMap (certificateCoefficient 529)) = 6 := by
  decide +kernel
private theorem certificate_530 : HammingWeight (l2CoefficientMap (certificateCoefficient 530)) = 6 := by
  decide +kernel
private theorem certificate_531 : HammingWeight (l2CoefficientMap (certificateCoefficient 531)) = 10 := by
  decide +kernel
private theorem certificate_532 : HammingWeight (l2CoefficientMap (certificateCoefficient 532)) = 6 := by
  decide +kernel
private theorem certificate_533 : HammingWeight (l2CoefficientMap (certificateCoefficient 533)) = 6 := by
  decide +kernel
private theorem certificate_534 : HammingWeight (l2CoefficientMap (certificateCoefficient 534)) = 6 := by
  decide +kernel
private theorem certificate_535 : HammingWeight (l2CoefficientMap (certificateCoefficient 535)) = 10 := by
  decide +kernel
private theorem certificate_536 : HammingWeight (l2CoefficientMap (certificateCoefficient 536)) = 6 := by
  decide +kernel
private theorem certificate_537 : HammingWeight (l2CoefficientMap (certificateCoefficient 537)) = 6 := by
  decide +kernel
private theorem certificate_538 : HammingWeight (l2CoefficientMap (certificateCoefficient 538)) = 6 := by
  decide +kernel
private theorem certificate_539 : HammingWeight (l2CoefficientMap (certificateCoefficient 539)) = 10 := by
  decide +kernel
private theorem certificate_540 : HammingWeight (l2CoefficientMap (certificateCoefficient 540)) = 10 := by
  decide +kernel
private theorem certificate_541 : HammingWeight (l2CoefficientMap (certificateCoefficient 541)) = 10 := by
  decide +kernel
private theorem certificate_542 : HammingWeight (l2CoefficientMap (certificateCoefficient 542)) = 10 := by
  decide +kernel
private theorem certificate_543 : HammingWeight (l2CoefficientMap (certificateCoefficient 543)) = 6 := by
  decide +kernel
private theorem certificate_544 : HammingWeight (l2CoefficientMap (certificateCoefficient 544)) = 4 := by
  decide +kernel
private theorem certificate_545 : HammingWeight (l2CoefficientMap (certificateCoefficient 545)) = 8 := by
  decide +kernel
private theorem certificate_546 : HammingWeight (l2CoefficientMap (certificateCoefficient 546)) = 8 := by
  decide +kernel
private theorem certificate_547 : HammingWeight (l2CoefficientMap (certificateCoefficient 547)) = 8 := by
  decide +kernel
private theorem certificate_548 : HammingWeight (l2CoefficientMap (certificateCoefficient 548)) = 4 := by
  decide +kernel
private theorem certificate_549 : HammingWeight (l2CoefficientMap (certificateCoefficient 549)) = 8 := by
  decide +kernel
private theorem certificate_550 : HammingWeight (l2CoefficientMap (certificateCoefficient 550)) = 8 := by
  decide +kernel
private theorem certificate_551 : HammingWeight (l2CoefficientMap (certificateCoefficient 551)) = 8 := by
  decide +kernel
private theorem certificate_552 : HammingWeight (l2CoefficientMap (certificateCoefficient 552)) = 8 := by
  decide +kernel
private theorem certificate_553 : HammingWeight (l2CoefficientMap (certificateCoefficient 553)) = 4 := by
  decide +kernel
private theorem certificate_554 : HammingWeight (l2CoefficientMap (certificateCoefficient 554)) = 8 := by
  decide +kernel
private theorem certificate_555 : HammingWeight (l2CoefficientMap (certificateCoefficient 555)) = 8 := by
  decide +kernel
private theorem certificate_556 : HammingWeight (l2CoefficientMap (certificateCoefficient 556)) = 8 := by
  decide +kernel
private theorem certificate_557 : HammingWeight (l2CoefficientMap (certificateCoefficient 557)) = 12 := by
  decide +kernel
private theorem certificate_558 : HammingWeight (l2CoefficientMap (certificateCoefficient 558)) = 8 := by
  decide +kernel
private theorem certificate_559 : HammingWeight (l2CoefficientMap (certificateCoefficient 559)) = 8 := by
  decide +kernel
private theorem certificate_560 : HammingWeight (l2CoefficientMap (certificateCoefficient 560)) = 6 := by
  decide +kernel
private theorem certificate_561 : HammingWeight (l2CoefficientMap (certificateCoefficient 561)) = 6 := by
  decide +kernel
private theorem certificate_562 : HammingWeight (l2CoefficientMap (certificateCoefficient 562)) = 6 := by
  decide +kernel
private theorem certificate_563 : HammingWeight (l2CoefficientMap (certificateCoefficient 563)) = 10 := by
  decide +kernel
private theorem certificate_564 : HammingWeight (l2CoefficientMap (certificateCoefficient 564)) = 6 := by
  decide +kernel
private theorem certificate_565 : HammingWeight (l2CoefficientMap (certificateCoefficient 565)) = 6 := by
  decide +kernel
private theorem certificate_566 : HammingWeight (l2CoefficientMap (certificateCoefficient 566)) = 6 := by
  decide +kernel
private theorem certificate_567 : HammingWeight (l2CoefficientMap (certificateCoefficient 567)) = 10 := by
  decide +kernel
private theorem certificate_568 : HammingWeight (l2CoefficientMap (certificateCoefficient 568)) = 6 := by
  decide +kernel
private theorem certificate_569 : HammingWeight (l2CoefficientMap (certificateCoefficient 569)) = 6 := by
  decide +kernel
private theorem certificate_570 : HammingWeight (l2CoefficientMap (certificateCoefficient 570)) = 10 := by
  decide +kernel
private theorem certificate_571 : HammingWeight (l2CoefficientMap (certificateCoefficient 571)) = 6 := by
  decide +kernel
private theorem certificate_572 : HammingWeight (l2CoefficientMap (certificateCoefficient 572)) = 10 := by
  decide +kernel
private theorem certificate_573 : HammingWeight (l2CoefficientMap (certificateCoefficient 573)) = 10 := by
  decide +kernel
private theorem certificate_574 : HammingWeight (l2CoefficientMap (certificateCoefficient 574)) = 6 := by
  decide +kernel
private theorem certificate_575 : HammingWeight (l2CoefficientMap (certificateCoefficient 575)) = 10 := by
  decide +kernel
theorem word_table_block_8 (j : Fin 64) : HammingWeight (l2CoefficientMap (certificateCoefficient (8 * 64 + j.val))) = certificateWeightBlock 8 j := by
  change HammingWeight (l2CoefficientMap (certificateCoefficient (8 * 64 + j.val))) = (![4, 8, 8, 8, 4, 8, 8, 8, 4, 8, 8, 8, 12, 8, 8, 8, 6, 6, 6, 10, 6, 6, 6, 10, 6, 6, 6, 10, 10, 10, 10, 6, 4, 8, 8, 8, 4, 8, 8, 8, 8, 4, 8, 8, 8, 12, 8, 8, 6, 6, 6, 10, 6, 6, 6, 10, 6, 6, 10, 6, 10, 10, 6, 10] : Fin 64 → Nat) j
  fin_cases j
  · exact certificate_512
  · exact certificate_513
  · exact certificate_514
  · exact certificate_515
  · exact certificate_516
  · exact certificate_517
  · exact certificate_518
  · exact certificate_519
  · exact certificate_520
  · exact certificate_521
  · exact certificate_522
  · exact certificate_523
  · exact certificate_524
  · exact certificate_525
  · exact certificate_526
  · exact certificate_527
  · exact certificate_528
  · exact certificate_529
  · exact certificate_530
  · exact certificate_531
  · exact certificate_532
  · exact certificate_533
  · exact certificate_534
  · exact certificate_535
  · exact certificate_536
  · exact certificate_537
  · exact certificate_538
  · exact certificate_539
  · exact certificate_540
  · exact certificate_541
  · exact certificate_542
  · exact certificate_543
  · exact certificate_544
  · exact certificate_545
  · exact certificate_546
  · exact certificate_547
  · exact certificate_548
  · exact certificate_549
  · exact certificate_550
  · exact certificate_551
  · exact certificate_552
  · exact certificate_553
  · exact certificate_554
  · exact certificate_555
  · exact certificate_556
  · exact certificate_557
  · exact certificate_558
  · exact certificate_559
  · exact certificate_560
  · exact certificate_561
  · exact certificate_562
  · exact certificate_563
  · exact certificate_564
  · exact certificate_565
  · exact certificate_566
  · exact certificate_567
  · exact certificate_568
  · exact certificate_569
  · exact certificate_570
  · exact certificate_571
  · exact certificate_572
  · exact certificate_573
  · exact certificate_574
  · exact certificate_575


end QEC.Distillation.BK15.CertifiedWeights


