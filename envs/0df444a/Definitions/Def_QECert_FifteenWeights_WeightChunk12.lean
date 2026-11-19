-- Prove2me | Definitions.Def_QECert_FifteenWeights_WeightChunk12
-- name    : QECert_FifteenWeights_WeightChunk12
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:57:24.182122+00:00
-- url     : https://prove2.me/theorems/100f61ae-bd40-45ba-ab33-04b2e698d28a
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
private theorem certificate_768 : HammingWeight (l2CoefficientMap (certificateCoefficient 768)) = 4 := by
  decide +kernel
private theorem certificate_769 : HammingWeight (l2CoefficientMap (certificateCoefficient 769)) = 8 := by
  decide +kernel
private theorem certificate_770 : HammingWeight (l2CoefficientMap (certificateCoefficient 770)) = 8 := by
  decide +kernel
private theorem certificate_771 : HammingWeight (l2CoefficientMap (certificateCoefficient 771)) = 8 := by
  decide +kernel
private theorem certificate_772 : HammingWeight (l2CoefficientMap (certificateCoefficient 772)) = 8 := by
  decide +kernel
private theorem certificate_773 : HammingWeight (l2CoefficientMap (certificateCoefficient 773)) = 8 := by
  decide +kernel
private theorem certificate_774 : HammingWeight (l2CoefficientMap (certificateCoefficient 774)) = 4 := by
  decide +kernel
private theorem certificate_775 : HammingWeight (l2CoefficientMap (certificateCoefficient 775)) = 8 := by
  decide +kernel
private theorem certificate_776 : HammingWeight (l2CoefficientMap (certificateCoefficient 776)) = 4 := by
  decide +kernel
private theorem certificate_777 : HammingWeight (l2CoefficientMap (certificateCoefficient 777)) = 8 := by
  decide +kernel
private theorem certificate_778 : HammingWeight (l2CoefficientMap (certificateCoefficient 778)) = 8 := by
  decide +kernel
private theorem certificate_779 : HammingWeight (l2CoefficientMap (certificateCoefficient 779)) = 8 := by
  decide +kernel
private theorem certificate_780 : HammingWeight (l2CoefficientMap (certificateCoefficient 780)) = 8 := by
  decide +kernel
private theorem certificate_781 : HammingWeight (l2CoefficientMap (certificateCoefficient 781)) = 8 := by
  decide +kernel
private theorem certificate_782 : HammingWeight (l2CoefficientMap (certificateCoefficient 782)) = 12 := by
  decide +kernel
private theorem certificate_783 : HammingWeight (l2CoefficientMap (certificateCoefficient 783)) = 8 := by
  decide +kernel
private theorem certificate_784 : HammingWeight (l2CoefficientMap (certificateCoefficient 784)) = 6 := by
  decide +kernel
private theorem certificate_785 : HammingWeight (l2CoefficientMap (certificateCoefficient 785)) = 6 := by
  decide +kernel
private theorem certificate_786 : HammingWeight (l2CoefficientMap (certificateCoefficient 786)) = 6 := by
  decide +kernel
private theorem certificate_787 : HammingWeight (l2CoefficientMap (certificateCoefficient 787)) = 10 := by
  decide +kernel
private theorem certificate_788 : HammingWeight (l2CoefficientMap (certificateCoefficient 788)) = 6 := by
  decide +kernel
private theorem certificate_789 : HammingWeight (l2CoefficientMap (certificateCoefficient 789)) = 10 := by
  decide +kernel
private theorem certificate_790 : HammingWeight (l2CoefficientMap (certificateCoefficient 790)) = 6 := by
  decide +kernel
private theorem certificate_791 : HammingWeight (l2CoefficientMap (certificateCoefficient 791)) = 6 := by
  decide +kernel
private theorem certificate_792 : HammingWeight (l2CoefficientMap (certificateCoefficient 792)) = 6 := by
  decide +kernel
private theorem certificate_793 : HammingWeight (l2CoefficientMap (certificateCoefficient 793)) = 6 := by
  decide +kernel
private theorem certificate_794 : HammingWeight (l2CoefficientMap (certificateCoefficient 794)) = 6 := by
  decide +kernel
private theorem certificate_795 : HammingWeight (l2CoefficientMap (certificateCoefficient 795)) = 10 := by
  decide +kernel
private theorem certificate_796 : HammingWeight (l2CoefficientMap (certificateCoefficient 796)) = 10 := by
  decide +kernel
private theorem certificate_797 : HammingWeight (l2CoefficientMap (certificateCoefficient 797)) = 6 := by
  decide +kernel
private theorem certificate_798 : HammingWeight (l2CoefficientMap (certificateCoefficient 798)) = 10 := by
  decide +kernel
private theorem certificate_799 : HammingWeight (l2CoefficientMap (certificateCoefficient 799)) = 10 := by
  decide +kernel
private theorem certificate_800 : HammingWeight (l2CoefficientMap (certificateCoefficient 800)) = 6 := by
  decide +kernel
private theorem certificate_801 : HammingWeight (l2CoefficientMap (certificateCoefficient 801)) = 6 := by
  decide +kernel
private theorem certificate_802 : HammingWeight (l2CoefficientMap (certificateCoefficient 802)) = 6 := by
  decide +kernel
private theorem certificate_803 : HammingWeight (l2CoefficientMap (certificateCoefficient 803)) = 10 := by
  decide +kernel
private theorem certificate_804 : HammingWeight (l2CoefficientMap (certificateCoefficient 804)) = 6 := by
  decide +kernel
private theorem certificate_805 : HammingWeight (l2CoefficientMap (certificateCoefficient 805)) = 10 := by
  decide +kernel
private theorem certificate_806 : HammingWeight (l2CoefficientMap (certificateCoefficient 806)) = 6 := by
  decide +kernel
private theorem certificate_807 : HammingWeight (l2CoefficientMap (certificateCoefficient 807)) = 6 := by
  decide +kernel
private theorem certificate_808 : HammingWeight (l2CoefficientMap (certificateCoefficient 808)) = 6 := by
  decide +kernel
private theorem certificate_809 : HammingWeight (l2CoefficientMap (certificateCoefficient 809)) = 6 := by
  decide +kernel
private theorem certificate_810 : HammingWeight (l2CoefficientMap (certificateCoefficient 810)) = 10 := by
  decide +kernel
private theorem certificate_811 : HammingWeight (l2CoefficientMap (certificateCoefficient 811)) = 6 := by
  decide +kernel
private theorem certificate_812 : HammingWeight (l2CoefficientMap (certificateCoefficient 812)) = 6 := by
  decide +kernel
private theorem certificate_813 : HammingWeight (l2CoefficientMap (certificateCoefficient 813)) = 10 := by
  decide +kernel
private theorem certificate_814 : HammingWeight (l2CoefficientMap (certificateCoefficient 814)) = 10 := by
  decide +kernel
private theorem certificate_815 : HammingWeight (l2CoefficientMap (certificateCoefficient 815)) = 10 := by
  decide +kernel
private theorem certificate_816 : HammingWeight (l2CoefficientMap (certificateCoefficient 816)) = 4 := by
  decide +kernel
private theorem certificate_817 : HammingWeight (l2CoefficientMap (certificateCoefficient 817)) = 8 := by
  decide +kernel
private theorem certificate_818 : HammingWeight (l2CoefficientMap (certificateCoefficient 818)) = 8 := by
  decide +kernel
private theorem certificate_819 : HammingWeight (l2CoefficientMap (certificateCoefficient 819)) = 8 := by
  decide +kernel
private theorem certificate_820 : HammingWeight (l2CoefficientMap (certificateCoefficient 820)) = 8 := by
  decide +kernel
private theorem certificate_821 : HammingWeight (l2CoefficientMap (certificateCoefficient 821)) = 8 := by
  decide +kernel
private theorem certificate_822 : HammingWeight (l2CoefficientMap (certificateCoefficient 822)) = 4 := by
  decide +kernel
private theorem certificate_823 : HammingWeight (l2CoefficientMap (certificateCoefficient 823)) = 8 := by
  decide +kernel
private theorem certificate_824 : HammingWeight (l2CoefficientMap (certificateCoefficient 824)) = 8 := by
  decide +kernel
private theorem certificate_825 : HammingWeight (l2CoefficientMap (certificateCoefficient 825)) = 4 := by
  decide +kernel
private theorem certificate_826 : HammingWeight (l2CoefficientMap (certificateCoefficient 826)) = 8 := by
  decide +kernel
private theorem certificate_827 : HammingWeight (l2CoefficientMap (certificateCoefficient 827)) = 8 := by
  decide +kernel
private theorem certificate_828 : HammingWeight (l2CoefficientMap (certificateCoefficient 828)) = 8 := by
  decide +kernel
private theorem certificate_829 : HammingWeight (l2CoefficientMap (certificateCoefficient 829)) = 8 := by
  decide +kernel
private theorem certificate_830 : HammingWeight (l2CoefficientMap (certificateCoefficient 830)) = 8 := by
  decide +kernel
private theorem certificate_831 : HammingWeight (l2CoefficientMap (certificateCoefficient 831)) = 12 := by
  decide +kernel
theorem word_table_block_12 (j : Fin 64) : HammingWeight (l2CoefficientMap (certificateCoefficient (12 * 64 + j.val))) = certificateWeightBlock 12 j := by
  change HammingWeight (l2CoefficientMap (certificateCoefficient (12 * 64 + j.val))) = (![4, 8, 8, 8, 8, 8, 4, 8, 4, 8, 8, 8, 8, 8, 12, 8, 6, 6, 6, 10, 6, 10, 6, 6, 6, 6, 6, 10, 10, 6, 10, 10, 6, 6, 6, 10, 6, 10, 6, 6, 6, 6, 10, 6, 6, 10, 10, 10, 4, 8, 8, 8, 8, 8, 4, 8, 8, 4, 8, 8, 8, 8, 8, 12] : Fin 64 → Nat) j
  fin_cases j
  · exact certificate_768
  · exact certificate_769
  · exact certificate_770
  · exact certificate_771
  · exact certificate_772
  · exact certificate_773
  · exact certificate_774
  · exact certificate_775
  · exact certificate_776
  · exact certificate_777
  · exact certificate_778
  · exact certificate_779
  · exact certificate_780
  · exact certificate_781
  · exact certificate_782
  · exact certificate_783
  · exact certificate_784
  · exact certificate_785
  · exact certificate_786
  · exact certificate_787
  · exact certificate_788
  · exact certificate_789
  · exact certificate_790
  · exact certificate_791
  · exact certificate_792
  · exact certificate_793
  · exact certificate_794
  · exact certificate_795
  · exact certificate_796
  · exact certificate_797
  · exact certificate_798
  · exact certificate_799
  · exact certificate_800
  · exact certificate_801
  · exact certificate_802
  · exact certificate_803
  · exact certificate_804
  · exact certificate_805
  · exact certificate_806
  · exact certificate_807
  · exact certificate_808
  · exact certificate_809
  · exact certificate_810
  · exact certificate_811
  · exact certificate_812
  · exact certificate_813
  · exact certificate_814
  · exact certificate_815
  · exact certificate_816
  · exact certificate_817
  · exact certificate_818
  · exact certificate_819
  · exact certificate_820
  · exact certificate_821
  · exact certificate_822
  · exact certificate_823
  · exact certificate_824
  · exact certificate_825
  · exact certificate_826
  · exact certificate_827
  · exact certificate_828
  · exact certificate_829
  · exact certificate_830
  · exact certificate_831


end QEC.Distillation.BK15.CertifiedWeights


