-- Prove2me | Definitions.Def_QECert_FifteenWeights_WeightChunk10
-- name    : QECert_FifteenWeights_WeightChunk10
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:57:14.941799+00:00
-- url     : https://prove2.me/theorems/52ce6b36-8b4e-44a6-9cbe-20f4aca46fd0
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
private theorem certificate_640 : HammingWeight (l2CoefficientMap (certificateCoefficient 640)) = 4 := by
  decide +kernel
private theorem certificate_641 : HammingWeight (l2CoefficientMap (certificateCoefficient 641)) = 8 := by
  decide +kernel
private theorem certificate_642 : HammingWeight (l2CoefficientMap (certificateCoefficient 642)) = 8 := by
  decide +kernel
private theorem certificate_643 : HammingWeight (l2CoefficientMap (certificateCoefficient 643)) = 8 := by
  decide +kernel
private theorem certificate_644 : HammingWeight (l2CoefficientMap (certificateCoefficient 644)) = 4 := by
  decide +kernel
private theorem certificate_645 : HammingWeight (l2CoefficientMap (certificateCoefficient 645)) = 8 := by
  decide +kernel
private theorem certificate_646 : HammingWeight (l2CoefficientMap (certificateCoefficient 646)) = 8 := by
  decide +kernel
private theorem certificate_647 : HammingWeight (l2CoefficientMap (certificateCoefficient 647)) = 8 := by
  decide +kernel
private theorem certificate_648 : HammingWeight (l2CoefficientMap (certificateCoefficient 648)) = 8 := by
  decide +kernel
private theorem certificate_649 : HammingWeight (l2CoefficientMap (certificateCoefficient 649)) = 8 := by
  decide +kernel
private theorem certificate_650 : HammingWeight (l2CoefficientMap (certificateCoefficient 650)) = 4 := by
  decide +kernel
private theorem certificate_651 : HammingWeight (l2CoefficientMap (certificateCoefficient 651)) = 8 := by
  decide +kernel
private theorem certificate_652 : HammingWeight (l2CoefficientMap (certificateCoefficient 652)) = 8 := by
  decide +kernel
private theorem certificate_653 : HammingWeight (l2CoefficientMap (certificateCoefficient 653)) = 8 := by
  decide +kernel
private theorem certificate_654 : HammingWeight (l2CoefficientMap (certificateCoefficient 654)) = 12 := by
  decide +kernel
private theorem certificate_655 : HammingWeight (l2CoefficientMap (certificateCoefficient 655)) = 8 := by
  decide +kernel
private theorem certificate_656 : HammingWeight (l2CoefficientMap (certificateCoefficient 656)) = 6 := by
  decide +kernel
private theorem certificate_657 : HammingWeight (l2CoefficientMap (certificateCoefficient 657)) = 6 := by
  decide +kernel
private theorem certificate_658 : HammingWeight (l2CoefficientMap (certificateCoefficient 658)) = 6 := by
  decide +kernel
private theorem certificate_659 : HammingWeight (l2CoefficientMap (certificateCoefficient 659)) = 10 := by
  decide +kernel
private theorem certificate_660 : HammingWeight (l2CoefficientMap (certificateCoefficient 660)) = 6 := by
  decide +kernel
private theorem certificate_661 : HammingWeight (l2CoefficientMap (certificateCoefficient 661)) = 6 := by
  decide +kernel
private theorem certificate_662 : HammingWeight (l2CoefficientMap (certificateCoefficient 662)) = 6 := by
  decide +kernel
private theorem certificate_663 : HammingWeight (l2CoefficientMap (certificateCoefficient 663)) = 10 := by
  decide +kernel
private theorem certificate_664 : HammingWeight (l2CoefficientMap (certificateCoefficient 664)) = 6 := by
  decide +kernel
private theorem certificate_665 : HammingWeight (l2CoefficientMap (certificateCoefficient 665)) = 10 := by
  decide +kernel
private theorem certificate_666 : HammingWeight (l2CoefficientMap (certificateCoefficient 666)) = 6 := by
  decide +kernel
private theorem certificate_667 : HammingWeight (l2CoefficientMap (certificateCoefficient 667)) = 6 := by
  decide +kernel
private theorem certificate_668 : HammingWeight (l2CoefficientMap (certificateCoefficient 668)) = 10 := by
  decide +kernel
private theorem certificate_669 : HammingWeight (l2CoefficientMap (certificateCoefficient 669)) = 6 := by
  decide +kernel
private theorem certificate_670 : HammingWeight (l2CoefficientMap (certificateCoefficient 670)) = 10 := by
  decide +kernel
private theorem certificate_671 : HammingWeight (l2CoefficientMap (certificateCoefficient 671)) = 10 := by
  decide +kernel
private theorem certificate_672 : HammingWeight (l2CoefficientMap (certificateCoefficient 672)) = 4 := by
  decide +kernel
private theorem certificate_673 : HammingWeight (l2CoefficientMap (certificateCoefficient 673)) = 8 := by
  decide +kernel
private theorem certificate_674 : HammingWeight (l2CoefficientMap (certificateCoefficient 674)) = 8 := by
  decide +kernel
private theorem certificate_675 : HammingWeight (l2CoefficientMap (certificateCoefficient 675)) = 8 := by
  decide +kernel
private theorem certificate_676 : HammingWeight (l2CoefficientMap (certificateCoefficient 676)) = 4 := by
  decide +kernel
private theorem certificate_677 : HammingWeight (l2CoefficientMap (certificateCoefficient 677)) = 8 := by
  decide +kernel
private theorem certificate_678 : HammingWeight (l2CoefficientMap (certificateCoefficient 678)) = 8 := by
  decide +kernel
private theorem certificate_679 : HammingWeight (l2CoefficientMap (certificateCoefficient 679)) = 8 := by
  decide +kernel
private theorem certificate_680 : HammingWeight (l2CoefficientMap (certificateCoefficient 680)) = 8 := by
  decide +kernel
private theorem certificate_681 : HammingWeight (l2CoefficientMap (certificateCoefficient 681)) = 8 := by
  decide +kernel
private theorem certificate_682 : HammingWeight (l2CoefficientMap (certificateCoefficient 682)) = 8 := by
  decide +kernel
private theorem certificate_683 : HammingWeight (l2CoefficientMap (certificateCoefficient 683)) = 4 := by
  decide +kernel
private theorem certificate_684 : HammingWeight (l2CoefficientMap (certificateCoefficient 684)) = 8 := by
  decide +kernel
private theorem certificate_685 : HammingWeight (l2CoefficientMap (certificateCoefficient 685)) = 8 := by
  decide +kernel
private theorem certificate_686 : HammingWeight (l2CoefficientMap (certificateCoefficient 686)) = 8 := by
  decide +kernel
private theorem certificate_687 : HammingWeight (l2CoefficientMap (certificateCoefficient 687)) = 12 := by
  decide +kernel
private theorem certificate_688 : HammingWeight (l2CoefficientMap (certificateCoefficient 688)) = 6 := by
  decide +kernel
private theorem certificate_689 : HammingWeight (l2CoefficientMap (certificateCoefficient 689)) = 6 := by
  decide +kernel
private theorem certificate_690 : HammingWeight (l2CoefficientMap (certificateCoefficient 690)) = 6 := by
  decide +kernel
private theorem certificate_691 : HammingWeight (l2CoefficientMap (certificateCoefficient 691)) = 10 := by
  decide +kernel
private theorem certificate_692 : HammingWeight (l2CoefficientMap (certificateCoefficient 692)) = 6 := by
  decide +kernel
private theorem certificate_693 : HammingWeight (l2CoefficientMap (certificateCoefficient 693)) = 6 := by
  decide +kernel
private theorem certificate_694 : HammingWeight (l2CoefficientMap (certificateCoefficient 694)) = 6 := by
  decide +kernel
private theorem certificate_695 : HammingWeight (l2CoefficientMap (certificateCoefficient 695)) = 10 := by
  decide +kernel
private theorem certificate_696 : HammingWeight (l2CoefficientMap (certificateCoefficient 696)) = 10 := by
  decide +kernel
private theorem certificate_697 : HammingWeight (l2CoefficientMap (certificateCoefficient 697)) = 6 := by
  decide +kernel
private theorem certificate_698 : HammingWeight (l2CoefficientMap (certificateCoefficient 698)) = 6 := by
  decide +kernel
private theorem certificate_699 : HammingWeight (l2CoefficientMap (certificateCoefficient 699)) = 6 := by
  decide +kernel
private theorem certificate_700 : HammingWeight (l2CoefficientMap (certificateCoefficient 700)) = 6 := by
  decide +kernel
private theorem certificate_701 : HammingWeight (l2CoefficientMap (certificateCoefficient 701)) = 10 := by
  decide +kernel
private theorem certificate_702 : HammingWeight (l2CoefficientMap (certificateCoefficient 702)) = 10 := by
  decide +kernel
private theorem certificate_703 : HammingWeight (l2CoefficientMap (certificateCoefficient 703)) = 10 := by
  decide +kernel
theorem word_table_block_10 (j : Fin 64) : HammingWeight (l2CoefficientMap (certificateCoefficient (10 * 64 + j.val))) = certificateWeightBlock 10 j := by
  change HammingWeight (l2CoefficientMap (certificateCoefficient (10 * 64 + j.val))) = (![4, 8, 8, 8, 4, 8, 8, 8, 8, 8, 4, 8, 8, 8, 12, 8, 6, 6, 6, 10, 6, 6, 6, 10, 6, 10, 6, 6, 10, 6, 10, 10, 4, 8, 8, 8, 4, 8, 8, 8, 8, 8, 8, 4, 8, 8, 8, 12, 6, 6, 6, 10, 6, 6, 6, 10, 10, 6, 6, 6, 6, 10, 10, 10] : Fin 64 → Nat) j
  fin_cases j
  · exact certificate_640
  · exact certificate_641
  · exact certificate_642
  · exact certificate_643
  · exact certificate_644
  · exact certificate_645
  · exact certificate_646
  · exact certificate_647
  · exact certificate_648
  · exact certificate_649
  · exact certificate_650
  · exact certificate_651
  · exact certificate_652
  · exact certificate_653
  · exact certificate_654
  · exact certificate_655
  · exact certificate_656
  · exact certificate_657
  · exact certificate_658
  · exact certificate_659
  · exact certificate_660
  · exact certificate_661
  · exact certificate_662
  · exact certificate_663
  · exact certificate_664
  · exact certificate_665
  · exact certificate_666
  · exact certificate_667
  · exact certificate_668
  · exact certificate_669
  · exact certificate_670
  · exact certificate_671
  · exact certificate_672
  · exact certificate_673
  · exact certificate_674
  · exact certificate_675
  · exact certificate_676
  · exact certificate_677
  · exact certificate_678
  · exact certificate_679
  · exact certificate_680
  · exact certificate_681
  · exact certificate_682
  · exact certificate_683
  · exact certificate_684
  · exact certificate_685
  · exact certificate_686
  · exact certificate_687
  · exact certificate_688
  · exact certificate_689
  · exact certificate_690
  · exact certificate_691
  · exact certificate_692
  · exact certificate_693
  · exact certificate_694
  · exact certificate_695
  · exact certificate_696
  · exact certificate_697
  · exact certificate_698
  · exact certificate_699
  · exact certificate_700
  · exact certificate_701
  · exact certificate_702
  · exact certificate_703


end QEC.Distillation.BK15.CertifiedWeights


