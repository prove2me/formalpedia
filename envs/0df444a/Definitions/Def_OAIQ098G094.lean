-- Prove2me | Definitions.Def_OAIQ098G094
-- name    : OAIQ098G094
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:06:10.58571+00:00
-- url     : https://prove2.me/theorems/b20d8938-8278-4592-80a7-eb3711aa304a
-- title:
--   Definitions bundle OAIQ098G094 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 431 declarations of OpenAI's Lean: 431 definitions. The definitions and types are `OAI.SharpPlanar.IntegerRoots.mid1001`, `OAI.SharpPlanar.IntegerRoots.mid1003`, `OAI.SharpPlanar.IntegerRoots.mid1005`, `OAI.SharpPlanar.IntegerRoots.mid1007`, `OAI.SharpPlanar.IntegerRoots.mid1009`, `OAI.SharpPlanar.IntegerRoots.mid101`, `OAI.SharpPlanar.IntegerRoots.mid1011`, `OAI.SharpPlanar.IntegerRoots.mid1013`, `OAI.SharpPlanar.IntegerRoots.mid1015`, `OAI.SharpPlanar.IntegerRoots.mid1017`, `OAI.SharpPlanar.IntegerRoots.mid1019`, `OAI.SharpPlanar.IntegerRoots.mid1021`, `OAI.SharpPlanar.IntegerRoots.mid1023`, `OAI.SharpPlanar.IntegerRoots.mid103`, `OAI.SharpPlanar.IntegerRoots.mid105`, `OAI.SharpPlanar.IntegerRoots.mid107`, `OAI.SharpPlanar.IntegerRoots.mid109`, `OAI.SharpPlanar.IntegerRoots.mid111`, `OAI.SharpPlanar.IntegerRoots.mid113`, `OAI.SharpPlanar.IntegerRoots.mid115`, `OAI.SharpPlanar.IntegerRoots.mid117`, `OAI.SharpPlanar.IntegerRoots.mid119`, `OAI.SharpPlanar.IntegerRoots.mid121`, `OAI.SharpPlanar.IntegerRoots.mid123`, `OAI.SharpPlanar.IntegerRoots.mid125`, `OAI.SharpPlanar.IntegerRoots.mid127`, `OAI.SharpPlanar.IntegerRoots.mid129`, `OAI.SharpPlanar.IntegerRoots.mid131`, `OAI.SharpPlanar.IntegerRoots.mid133`, `OAI.SharpPlanar.IntegerRoots.mid135`, `OAI.SharpPlanar.IntegerRoots.mid137`, `OAI.SharpPlanar.IntegerRoots.mid139`, `OAI.SharpPlanar.IntegerRoots.mid141`, `OAI.SharpPlanar.IntegerRoots.mid143`, `OAI.SharpPlanar.IntegerRoots.mid145`, `OAI.SharpPlanar.IntegerRoots.mid147`, `OAI.SharpPlanar.IntegerRoots.mid149`, `OAI.SharpPlanar.IntegerRoots.mid15`, `OAI.SharpPlanar.IntegerRoots.mid151`, `OAI.SharpPlanar.IntegerRoots.mid153` and 391 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Roots`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Roots.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G064` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.IntegerCompact.weightRows_contains_g`, `OAI.SharpPlanar.IntegerGrid.gridRows_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_10_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_8_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_9_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_7_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_8_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_10_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_11_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_15_contains_g` and `OAI.SharpPlanar.IntegerGrid.row5_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G064

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Roots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Certified roots of unity

Integer enclosures for the 1024th roots of unity, obtained from a certified
Taylor approximation and repeated squaring.
-/

namespace SharpPlanar
namespace IntegerRoots
open IntegerIntervals
def mid3 : CBox := root2
def mid5 : CBox := root4
def mid7 : CBox := root6
def mid9 : CBox := root8
def mid15 : CBox := root14
def mid17 : CBox := root16
def mid19 : CBox := root18
def mid21 : CBox := root20
def mid23 : CBox := root22
def mid25 : CBox := root24
def mid27 : CBox := root26
def mid29 : CBox := root28
def mid31 : CBox := root30
def mid33 : CBox := root32
def mid35 : CBox := root34
def mid37 : CBox := root36
def mid39 : CBox := root38
def mid41 : CBox := root40
def mid43 : CBox := root42
def mid45 : CBox := root44
def mid47 : CBox := root46
def mid49 : CBox := root48
def mid51 : CBox := root50
def mid53 : CBox := root52
def mid55 : CBox := root54
def mid57 : CBox := root56
def mid59 : CBox := root58
def mid61 : CBox := root60
def mid63 : CBox := root62
def mid65 : CBox := root64
def mid67 : CBox := root66
def mid69 : CBox := root68
def mid71 : CBox := root70
def mid73 : CBox := root72
def mid75 : CBox := root74
def mid77 : CBox := root76
def mid79 : CBox := root78
def mid81 : CBox := root80
def mid83 : CBox := root82
def mid85 : CBox := root84
def mid87 : CBox := root86
def mid89 : CBox := root88
def mid91 : CBox := root90
def mid93 : CBox := root92
def mid95 : CBox := root94
def mid97 : CBox := root96
def mid99 : CBox := root98
def mid101 : CBox := root100
def mid103 : CBox := root102
def mid105 : CBox := root104
def mid107 : CBox := root106
def mid109 : CBox := root108
def mid111 : CBox := root110
def mid113 : CBox := root112
def mid115 : CBox := root114
def mid117 : CBox := root116
def mid119 : CBox := root118
def mid121 : CBox := root120
def mid123 : CBox := root122
def mid125 : CBox := root124
def mid127 : CBox := root126
def mid129 : CBox := root128
def mid131 : CBox := root130
def mid133 : CBox := root132
def mid135 : CBox := root134
def mid137 : CBox := root136
def mid139 : CBox := root138
def mid141 : CBox := root140
def mid143 : CBox := root142
def mid145 : CBox := root144
def mid147 : CBox := root146
def mid149 : CBox := root148
def mid151 : CBox := root150
def mid153 : CBox := root152
def mid155 : CBox := root154
def mid157 : CBox := root156
def mid159 : CBox := root158
def mid161 : CBox := root160
def mid163 : CBox := root162
def mid165 : CBox := root164
def mid167 : CBox := root166
def mid321 : CBox := root320
def mid323 : CBox := root322
def mid325 : CBox := root324
def mid327 : CBox := root326
def mid329 : CBox := root328
def mid331 : CBox := root330
def mid333 : CBox := root332
def mid335 : CBox := root334
def mid337 : CBox := root336
def mid339 : CBox := root338
def mid341 : CBox := root340
def mid343 : CBox := root342
def mid345 : CBox := root344
def mid347 : CBox := root346
def mid349 : CBox := root348
def mid351 : CBox := root350
def mid353 : CBox := root352
def mid355 : CBox := root354
def mid357 : CBox := root356
def mid359 : CBox := root358
def mid361 : CBox := root360
def mid363 : CBox := root362
def mid365 : CBox := root364
def mid367 : CBox := root366
def mid369 : CBox := root368
def mid371 : CBox := root370
def mid373 : CBox := root372
def mid375 : CBox := root374
def mid377 : CBox := root376
def mid379 : CBox := root378
def mid381 : CBox := root380
def mid383 : CBox := root382
def mid385 : CBox := root384
def mid387 : CBox := root386
def mid389 : CBox := root388
def mid391 : CBox := root390
def mid393 : CBox := root392
def mid395 : CBox := root394
def mid397 : CBox := root396
def mid399 : CBox := root398
def mid401 : CBox := root400
def mid403 : CBox := root402
def mid405 : CBox := root404
def mid407 : CBox := root406
def mid409 : CBox := root408
def mid411 : CBox := root410
def mid413 : CBox := root412
def mid415 : CBox := root414
def mid417 : CBox := root416
def mid419 : CBox := root418
def mid421 : CBox := root420
def mid423 : CBox := root422
def mid425 : CBox := root424
def mid427 : CBox := root426
def mid429 : CBox := root428
def mid431 : CBox := root430
def mid433 : CBox := root432
def mid435 : CBox := root434
def mid437 : CBox := root436
def mid439 : CBox := root438
def mid441 : CBox := root440
def mid443 : CBox := root442
def mid445 : CBox := root444
def mid447 : CBox := root446
def mid449 : CBox := root448
def mid451 : CBox := root450
def mid453 : CBox := root452
def mid455 : CBox := root454
def mid457 : CBox := root456
def mid459 : CBox := root458
def mid461 : CBox := root460
def mid463 : CBox := root462
def mid465 : CBox := root464
def mid467 : CBox := root466
def mid469 : CBox := root468
def mid471 : CBox := root470
def mid473 : CBox := root472
def mid475 : CBox := root474
def mid477 : CBox := root476
def mid479 : CBox := root478
def mid481 : CBox := root480
def mid483 : CBox := root482
def mid485 : CBox := root484
def mid487 : CBox := root486
def mid489 : CBox := root488
def mid491 : CBox := root490
def mid493 : CBox := root492
def mid495 : CBox := root494
def mid497 : CBox := root496
def mid499 : CBox := root498
def mid501 : CBox := root500
def mid503 : CBox := root502
def mid505 : CBox := root504
def mid507 : CBox := root506
def mid509 : CBox := root508
def mid511 : CBox := root510
def mid515 : CBox := root514
def mid517 : CBox := root516
def mid519 : CBox := root518
def mid521 : CBox := root520
def mid523 : CBox := root522
def mid525 : CBox := root524
def mid527 : CBox := root526
def mid529 : CBox := root528
def mid531 : CBox := root530
def mid533 : CBox := root532
def mid535 : CBox := root534
def mid537 : CBox := root536
def mid539 : CBox := root538
def mid541 : CBox := root540
def mid543 : CBox := root542
def mid545 : CBox := root544
def mid547 : CBox := root546
def mid549 : CBox := root548
def mid551 : CBox := root550
def mid553 : CBox := root552
def mid555 : CBox := root554
def mid557 : CBox := root556
def mid559 : CBox := root558
def mid561 : CBox := root560
def mid563 : CBox := root562
def mid565 : CBox := root564
def mid567 : CBox := root566
def mid569 : CBox := root568
def mid571 : CBox := root570
def mid573 : CBox := root572
def mid575 : CBox := root574
def mid577 : CBox := root576
def mid579 : CBox := root578
def mid581 : CBox := root580
def mid583 : CBox := root582
def mid585 : CBox := root584
def mid587 : CBox := root586
def mid589 : CBox := root588
def mid591 : CBox := root590
def mid593 : CBox := root592
def mid595 : CBox := root594
def mid597 : CBox := root596
def mid599 : CBox := root598
def mid601 : CBox := root600
def mid603 : CBox := root602
def mid605 : CBox := root604
def mid607 : CBox := root606
def mid609 : CBox := root608
def mid611 : CBox := root610
def mid613 : CBox := root612
def mid615 : CBox := root614
def mid617 : CBox := root616
def mid619 : CBox := root618
def mid621 : CBox := root620
def mid623 : CBox := root622
def mid625 : CBox := root624
def mid627 : CBox := root626
def mid629 : CBox := root628
def mid631 : CBox := root630
def mid633 : CBox := root632
def mid635 : CBox := root634
def mid637 : CBox := root636
def mid639 : CBox := root638
def mid641 : CBox := root640
def mid643 : CBox := root642
def mid645 : CBox := root644
def mid647 : CBox := root646
def mid649 : CBox := root648
def mid651 : CBox := root650
def mid653 : CBox := root652
def mid655 : CBox := root654
def mid657 : CBox := root656
def mid659 : CBox := root658
def mid661 : CBox := root660
def mid663 : CBox := root662
def mid665 : CBox := root664
def mid667 : CBox := root666
def mid669 : CBox := root668
def mid671 : CBox := root670
def mid673 : CBox := root672
def mid675 : CBox := root674
def mid677 : CBox := root676
def mid679 : CBox := root678
def mid681 : CBox := root680
def mid683 : CBox := root682
def mid685 : CBox := root684
def mid687 : CBox := root686
def mid689 : CBox := root688
def mid691 : CBox := root690
def mid693 : CBox := root692
def mid695 : CBox := root694
def mid697 : CBox := root696
def mid699 : CBox := root698
def mid701 : CBox := root700
def mid703 : CBox := root702
def mid705 : CBox := root704
def mid707 : CBox := root706
def mid709 : CBox := root708
def mid711 : CBox := root710
def mid713 : CBox := root712
def mid715 : CBox := root714
def mid717 : CBox := root716
def mid719 : CBox := root718
def mid721 : CBox := root720
def mid723 : CBox := root722
def mid725 : CBox := root724
def mid727 : CBox := root726
def mid729 : CBox := root728
def mid731 : CBox := root730
def mid733 : CBox := root732
def mid735 : CBox := root734
def mid737 : CBox := root736
def mid739 : CBox := root738
def mid741 : CBox := root740
def mid743 : CBox := root742
def mid745 : CBox := root744
def mid747 : CBox := root746
def mid749 : CBox := root748
def mid751 : CBox := root750
def mid753 : CBox := root752
def mid755 : CBox := root754
def mid757 : CBox := root756
def mid759 : CBox := root758
def mid761 : CBox := root760
def mid763 : CBox := root762
def mid765 : CBox := root764
def mid767 : CBox := root766
def mid771 : CBox := root770
def mid773 : CBox := root772
def mid775 : CBox := root774
def mid777 : CBox := root776
def mid779 : CBox := root778
def mid781 : CBox := root780
def mid783 : CBox := root782
def mid785 : CBox := root784
def mid787 : CBox := root786
def mid789 : CBox := root788
def mid791 : CBox := root790
def mid793 : CBox := root792
def mid795 : CBox := root794
def mid797 : CBox := root796
def mid799 : CBox := root798
def mid801 : CBox := root800
def mid803 : CBox := root802
def mid805 : CBox := root804
def mid807 : CBox := root806
def mid809 : CBox := root808
def mid811 : CBox := root810
def mid813 : CBox := root812
def mid815 : CBox := root814
def mid817 : CBox := root816
def mid819 : CBox := root818
def mid821 : CBox := root820
def mid823 : CBox := root822
def mid825 : CBox := root824
def mid827 : CBox := root826
def mid829 : CBox := root828
def mid831 : CBox := root830
def mid833 : CBox := root832
def mid835 : CBox := root834
def mid837 : CBox := root836
def mid839 : CBox := root838
def mid841 : CBox := root840
def mid843 : CBox := root842
def mid845 : CBox := root844
def mid847 : CBox := root846
def mid849 : CBox := root848
def mid851 : CBox := root850
def mid853 : CBox := root852
def mid855 : CBox := root854
def mid857 : CBox := root856
def mid859 : CBox := root858
def mid861 : CBox := root860
def mid863 : CBox := root862
def mid865 : CBox := root864
def mid867 : CBox := root866
def mid869 : CBox := root868
def mid871 : CBox := root870
def mid873 : CBox := root872
def mid875 : CBox := root874
def mid877 : CBox := root876
def mid879 : CBox := root878
def mid881 : CBox := root880
def mid883 : CBox := root882
def mid885 : CBox := root884
def mid887 : CBox := root886
def mid889 : CBox := root888
def mid891 : CBox := root890
def mid893 : CBox := root892
def mid895 : CBox := root894
def mid897 : CBox := root896
def mid899 : CBox := root898
def mid901 : CBox := root900
def mid903 : CBox := root902
def mid905 : CBox := root904
def mid907 : CBox := root906
def mid909 : CBox := root908
def mid911 : CBox := root910
def mid913 : CBox := root912
def mid915 : CBox := root914
def mid917 : CBox := root916
def mid919 : CBox := root918
def mid921 : CBox := root920
def mid923 : CBox := root922
def mid925 : CBox := root924
def mid927 : CBox := root926
def mid929 : CBox := root928
def mid931 : CBox := root930
def mid933 : CBox := root932
def mid935 : CBox := root934
def mid937 : CBox := root936
def mid939 : CBox := root938
def mid941 : CBox := root940
def mid943 : CBox := root942
def mid945 : CBox := root944
def mid947 : CBox := root946
def mid949 : CBox := root948
def mid951 : CBox := root950
def mid953 : CBox := root952
def mid955 : CBox := root954
def mid957 : CBox := root956
def mid959 : CBox := root958
def mid961 : CBox := root960
def mid963 : CBox := root962
def mid965 : CBox := root964
def mid967 : CBox := root966
def mid969 : CBox := root968
def mid971 : CBox := root970
def mid973 : CBox := root972
def mid975 : CBox := root974
def mid977 : CBox := root976
def mid979 : CBox := root978
def mid981 : CBox := root980
def mid983 : CBox := root982
def mid985 : CBox := root984
def mid987 : CBox := root986
def mid989 : CBox := root988
def mid991 : CBox := root990
def mid993 : CBox := root992
def mid995 : CBox := root994
def mid997 : CBox := root996
def mid999 : CBox := root998
def mid1001 : CBox := root1000
def mid1003 : CBox := root1002
def mid1005 : CBox := root1004
def mid1007 : CBox := root1006
def mid1009 : CBox := root1008
def mid1011 : CBox := root1010
def mid1013 : CBox := root1012
def mid1015 : CBox := root1014
def mid1017 : CBox := root1016
def mid1019 : CBox := root1018
def mid1021 : CBox := root1020
def mid1023 : CBox := root1022
end IntegerRoots
end SharpPlanar

end OAI
end


