-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch117
-- name    : Polychromatic418967fa_Branch117
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:11:36.77143+00:00
-- url     : https://prove2.me/theorems/d694cbdb-fd90-4ccc-985f-f7860101d936
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_117 : allB 117 117 :=
  allB_succ' 2 116 117 (Eq.refl Bool.true) (allA_succ_of_accept 1 116 117 (accept_3_4 1 116 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116 117)) (allB_succ' 3 115 117 (Eq.refl Bool.true) (allA_succ_of_accept 2 115 117
  (accept_3_5 2 115 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 117
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 115 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 115 117))) (allB_succ' 4 114 117 (Eq.refl Bool.true) (allA_succ_of_gcd 3 114 117 3 1 38 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 114 117
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 114 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 114 117 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 114 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 114 117)))) (allB_succ' 5 113 117 (Eq.refl Bool.true) (allA_succ_of_accept 4
  113 117 (accept_3_4 4 113 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 117
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 113 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 113 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 113 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 117 (accept_3_4 1 113 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 113 117))))) (allB_succ' 6 112 117 (Eq.refl Bool.true) (allA_succ_of_accept 5 112 117
  (accept_3_5 5 112 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 117
  (Polychromatic418967fa.accept_10_4_2_7_1_373 4 112 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 112 117 (Polychromatic418967fa.accept_15_3_7_12_1_372 3 112 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 117 (accept_3_5 2 112 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 112 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 112 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 117)))))) (allB_succ' 7 111 117 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 111 117 3 2 37 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 111 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 111 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 111 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 117 3 1 37 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 111 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 111 117))))))) (allB_succ' 8 110 117 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 117 (accept_3_4 7 110 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  110 117 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 110 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 110 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 110 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 117 (accept_3_4 4 110 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 117
  (Polychromatic418967fa.accept_15_2_5_12_1_369 2 110 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 117 (accept_3_4 1 110 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  117)))))))) (allB_succ' 9 109 117 (Eq.refl Bool.true) (allA_succ_of_accept 8 109 117 (accept_3_5 8 109 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 117 (Polychromatic418967fa.accept_15_7_4_12_1_2530 7 109
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 117
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 109 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 117 (accept_3_5 5 109 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 109 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 117 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 109 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 117 (accept_3_5 2 109 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 109 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109 117))))))))) (allB_succ' 10 108 117 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 108 117 9 1 12 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 108 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 108 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 117 (Polychromatic418967fa.accept_15_7_3_12_1_365
  7 108 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 117 3 2 36 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 117
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 108 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 117 (Polychromatic418967fa.accept_16_4_12_5_1_2287 4 108 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 108 117 3 1 36 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 108 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 108 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 117
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 108 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 117)))))))))) (allB_succ' 11 107 117 (Eq.refl Bool.true) (allA_succ_of_accept 10 107 117 (accept_3_4 10
  107 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 117
  (Polychromatic418967fa.accept_16_9_11_5_1_2279 9 107 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 107 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 107 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 117 (accept_3_4 7 107 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 107 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 117 (Polychromatic418967fa.accept_15_5_2_12_1_2543
  5 107 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 117 (accept_3_4 4
  107 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 117
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 107 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 107 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 117 (accept_3_4 1 107 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 107 117))))))))))) (allB_succ' 12 106 117 (Eq.refl Bool.true) (allA_succ_of_accept 11 106 117
  (accept_3_5 11 106 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 106 117
  (Polychromatic418967fa.accept_7_3_1_5_1_44 10 106 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 106 117 (Polychromatic418967fa.accept_19_9_11_3_1_5580 9 106 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 117 (accept_3_5 8 106 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 106 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 106 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 6
  106 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 106 117 (accept_3_5 5 106
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 106 117
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 106 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 106 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 117 (accept_3_5 2 106 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 106 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 106 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 117)))))))))))) (allB_succ' 13 105 117 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 105 117 3 4 35 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 105 117 (Polychromatic418967fa.accept_16_11_9_5_1_4412 11 105 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 117 (Polychromatic418967fa.accept_18_10_15_9_1_1054 10 105
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 117 3 3 35 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 117
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 105 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 117 (Polychromatic418967fa.accept_19_7_10_3_1_4149 7 105 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 117 3 2 35 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 105 117 (Polychromatic418967fa.accept_18_5_15_9_1_1919 5 105 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 117
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 105 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 105 117 3 1 35 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 105 117 (Polychromatic418967fa.accept_10_2_5_7_1_1124 2 105 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 117 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 105 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105 117))))))))))))) (allB_succ' 14 104 117
  (Eq.refl Bool.true) (allA_succ_of_gcd 13 104 117 13 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 12 104 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 104 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 117
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 104 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 117 (accept_3_4 10 104 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 117 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 104 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 104 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 117 (accept_3_4 7 104 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 117 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 104 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 117
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 104 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 117 (accept_3_4 4 104 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 117 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 104 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 104 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 117 (accept_3_4 1 104 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104 117)))))))))))))) (allB_succ' 15 103 117 (Eq.refl Bool.true) (allA_succ_of_accept
  14 103 117 (accept_3_5 14 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 117
  (Polychromatic418967fa.accept_19_13_8_3_1_2906 13 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 103 117 (Polychromatic418967fa.accept_16_12_7_5_1_1412 12 103 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 117 (accept_3_5 11 103 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 103 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 103 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 117 (Polychromatic418967fa.accept_17_9_1_15_1_3156
  9 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 117 (accept_3_5 8
  103 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 117
  (Polychromatic418967fa.accept_21_7_19_12_1_5579 7 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 103 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 117 (accept_3_5 5 103 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 103 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 103 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 117 (Polychromatic418967fa.accept_11_3_4_7_1_114 3
  103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 117 (accept_3_5 2 103
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 117
  (Polychromatic418967fa.accept_15_1_13_12_1_347 1 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 103 117))))))))))))))) (allB_succ' 16 102 117 (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 117 3 5 34 39
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 102 117
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 102 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 102 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 117 3 4 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  102 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 117
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 102 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 102 117 3 3 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 102 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 102 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 102 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 117 3 2 34 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 117
  (Polychromatic418967fa.accept_10_5_2_7_1_345 5 102 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 117 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 102 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 102 117 3 1 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 102 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 102 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 117
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 102 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 102 117)))))))))))))))) (allB_succ' 17 101 117 (Eq.refl Bool.true) (allA_succ_of_accept 16 101 117
  (accept_3_4 16 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 117
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 101 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 101 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 117 (accept_3_4 13 101 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 101 117 (Polychromatic418967fa.accept_14_12_3_5_1_1868 12 101 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 117
  (Polychromatic418967fa.accept_17_11_16_15_1_5467 11 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 117 (accept_3_4 10 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 101 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 101 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 117 (accept_3_4 7 101 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 117 (Polychromatic418967fa.accept_10_6_1_7_1_342 6
  101 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 117
  (Polychromatic418967fa.accept_19_5_6_3_1_5578 5 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 117 (accept_3_4 4 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 117 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 101 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 117 (accept_3_4 1 101 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101 117))))))))))))))))) (allB_succ' 18 100 117 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 100 117 (accept_3_5 17 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 100 117 (Polychromatic418967fa.accept_19_16_5_3_1_1813 16 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 100 117 (Polychromatic418967fa.accept_16_15_4_5_1_1411 15 100 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 100 117 (accept_3_5 14 100 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 100 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 100 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 117
  (Polychromatic418967fa.accept_16_12_4_5_1_2273 12 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 100 117 (accept_3_5 11 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 100 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 100 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 100 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 117 (accept_3_5 8 100 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 100 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 100 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 117
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 100 117 (accept_3_5 5 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  100 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 100 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 100 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 117 (accept_3_5 2 100 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 100 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 100 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 117)))))))))))))))))) (allB_succ' 19 99 117 (Eq.refl
  Bool.true) (allA_succ_of_gcd 18 99 117 9 2 11 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 99 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 99 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 117
  (Polychromatic418967fa.accept_17_16_14_15_1_1250 16 99 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 99 117 3 5 33 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 99 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 13
  99 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 117 3 4 33 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 117
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 99 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 117 9 1 11 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 117 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 99 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 117
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 99 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 117 3 2 33 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 99 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 99 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 117 3 1 33 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 117 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 99 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99 117))))))))))))))))))) (allB_succ' 20 98 117 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 98 117 (accept_3_4 19 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 117 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 98 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 117 (accept_3_4 16 98 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 117
  (Polychromatic418967fa.accept_11_3_10_7_1_129 14 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 117 (accept_3_4 13 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 117 (Polychromatic418967fa.accept_22_12_10_7_1_2604 12 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 117 (accept_3_4 10 98 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 117 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 98 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 117
  (Polychromatic418967fa.accept_17_8_13_15_1_2143 8 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 117 (accept_3_4 7 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  117 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 98 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 117 (accept_3_4 4 98 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 117 (Polychromatic418967fa.accept_17_2_13_15_1_4349
  2 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 117 (accept_3_4 1 98
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98 117)))))))))))))))))))) (allB_succ' 21 97 117 (Eq.refl
  Bool.true) (allA_succ_of_accept 20 97 117 (accept_3_5 20 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 97 117 (Polychromatic418967fa.accept_15_4_7_12_1_5538 19 97 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 97 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 117 (accept_3_5 17 97 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 117
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 117 (accept_3_5 14 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 117 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 117 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 97 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 117 (accept_3_5 11 97 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 97 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 117
  (Polychromatic418967fa.accept_16_9_1_5_1_2282 9 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 117 (accept_3_5 8 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  117 (Polychromatic418967fa.accept_23_7_5_2_1_5577 7 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 117 (Polychromatic418967fa.accept_14_6_13_5_1_534 6 97 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 117 (accept_3_5 5 97 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 117
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 117 (accept_3_5 2 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  117 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 117))))))))))))))))))))) (allB_succ' 22 96 117 (Eq.refl Bool.true) (allA_succ_of_gcd 21 96 117 3 7 32 39
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 96 117
  (Polychromatic418967fa.accept_15_5_6_12_1_916 20 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 117 (Polychromatic418967fa.accept_18_1_6_9_1_2001 19 96 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 117 3 6 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 117 (Polychromatic418967fa.accept_14_3_12_5_1_153 17 96 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 117
  (Polychromatic418967fa.accept_17_16_11_15_1_4353 16 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 96 117 3 5 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 96 117 (Polychromatic418967fa.accept_18_14_6_9_1_1950 14 96 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 117 (Polychromatic418967fa.accept_10_3_6_7_1_2188
  13 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 117 3 4 32 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 117
  (Polychromatic418967fa.accept_10_1_6_7_1_710 11 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 117 (Polychromatic418967fa.accept_14_10_12_5_1_3466 10 96 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 96 117 3 3 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 96 117 (Polychromatic418967fa.accept_18_8_6_9_1_5576 8 96 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 117
  (Polychromatic418967fa.accept_14_7_12_5_1_1861 7 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 117 3 2 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 117 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 96 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 117 (Polychromatic418967fa.accept_11_4_8_7_1_819 4 96 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 117 3 1 32 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 117
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 96 117 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 96 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96 117)))))))))))))))))))))) (allB_succ' 23 95 117 (Eq.refl Bool.true)
  (allA_succ_of_accept 22 95 117 (accept_3_4 22 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 117 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 95 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 117 (accept_3_4 19 95 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 117
  (Polychromatic418967fa.accept_15_2_5_12_1_369 17 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 117 (accept_3_4 16 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 117 (accept_3_4 13 95 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 117 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 95 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 117
  (Polychromatic418967fa.accept_27_11_14_9_1_5575 11 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 117 (accept_3_4 10 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 117 (accept_3_4 7 95 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 117
  (Polychromatic418967fa.accept_17_5_10_15_1_5574 5 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 117 (accept_3_4 4 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  117 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 117 (accept_3_4 1 95 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95 117))))))))))))))))))))))) (allB_succ' 24 94 117 (Eq.refl Bool.true) (allA_succ_of_accept 23
  94 117 (accept_3_5 23 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 117
  (Polychromatic418967fa.accept_7_1_3_5_1_33 22 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 94 117 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 94 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 117 (accept_3_5 20 94 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 94 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 117 (Polychromatic418967fa.accept_12_6_10_9_1_531
  18 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 117 (accept_3_5 17
  94 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 117
  (Polychromatic418967fa.accept_7_2_3_5_1_34 16 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 94 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 117 (accept_3_5 14 94 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 94 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 94 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 117 (Polychromatic418967fa.accept_10_2_4_7_1_352
  12 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 117 (accept_3_5 11
  94 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 117
  (Polychromatic418967fa.accept_16_10_14_5_1_5496 10 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 94 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 94 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 117 (accept_3_5 8 94 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 94 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 117 (Polychromatic418967fa.accept_12_6_10_9_1_531 6
  94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 117 (accept_3_5 5 94 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94 117 (Polychromatic418967fa.accept_19_4_18_3_1_5553
  4 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 94 117 (accept_3_5 2 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94
  117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 117)))))))))))))))))))))))) (allB_succ' 25 93 117 (Eq.refl Bool.true) (allA_succ_of_gcd 24 93 117 3 8 31
  39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 117
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 93 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 117 (Polychromatic418967fa.accept_15_7_3_12_1_365 22 93 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 93 117 3 7 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 93 117 (Polychromatic418967fa.accept_11_9_5_7_1_815 20 93 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 117
  (Polychromatic418967fa.accept_18_1_3_9_1_328 19 93 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 93 117 3 6 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 93 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 93 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 117 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 93 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 117 3 5 31 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 117
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 93 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 117 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 93 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 117 3 4 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 93 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 117
  (Polychromatic418967fa.accept_7_3_2_5_1_147 10 93 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 93 117 3 3 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 93 117 (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 93 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 117 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 93 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 117 3 2 31 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 117
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 93 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 93 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 117 3 1 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 117 (Polychromatic418967fa.accept_15_2_3_12_1_891 2 93 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 117
  (Polychromatic418967fa.accept_16_1_13_5_1_2280 1 93 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 93 117))))))))))))))))))))))))) (allB_succ' 26 92 117 (Eq.refl Bool.true) (allA_succ_of_accept 25 92 117
  (accept_3_4 25 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 92 117
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 92 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 117 (accept_3_4 22 92 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 92 117 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 92 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 20
  92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 92 117 (accept_3_4 19 92
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 92 117
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 92 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 117 (accept_3_4 16 92 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 92 117 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 92 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 117 (Polychromatic418967fa.accept_10_4_2_7_1_373
  14 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 92 117 (accept_3_4 13
  92 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 92 117
  (Polychromatic418967fa.accept_26_12_14_13_1_5573 12 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 117 (accept_3_4 10 92 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 92 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 117
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 117 (accept_3_4 7 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  117 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 117 (accept_3_4 4 92 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 92 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 117 (Polychromatic418967fa.accept_17_2_7_15_1_5525
  2 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 117 (accept_3_4 1 92
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92 117)))))))))))))))))))))))))) (allB_succ' 27 91 117 (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 91 117 13 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 91 117 (Polychromatic418967fa.accept_16_9_11_5_1_2279 25 91 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 117 (Polychromatic418967fa.accept_10_4_1_7_1_371
  24 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 117 (accept_3_5 23
  91 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 91 117 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 91 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 117 (accept_3_5 20 91 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 91 117 (Polychromatic418967fa.accept_15_4_1_12_1_914 19 91 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 117 (accept_3_5 17 91
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 117 (Polychromatic418967fa.accept_6_4_1_3_1_77
  16 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 117
  (Polychromatic418967fa.accept_11_4_3_7_1_828 15 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 117 (accept_3_5 14 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 91
  117 13 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12
  91 117 (Polychromatic418967fa.accept_14_12_7_5_1_1107 12 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 91 117 (accept_3_5 11 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 91 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 117 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 91 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 117 (accept_3_5 8 91 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 117 (Polychromatic418967fa.accept_16_7_11_5_1_4402
  7 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 117 (accept_3_5 5 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 117 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 91 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 117 (accept_3_5 2 91 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 117 (Polychromatic418967fa.accept_20_1_11_17_1_1639 1 91 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 117))))))))))))))))))))))))))) (allB_succ' 28 90 117 (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 90 117 9 3 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 26 90 117 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 90 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 25
  90 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 117 3 8 30 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 90 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 117 3 7 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 90 117 (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 90 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 117 9 2 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 117 (Polychromatic418967fa.accept_19_17_14_3_1_5572 17 90 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 117 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 90 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 117 3 5 30 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 117
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 90 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 117 (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 90 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 117 3 4 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 117
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 90 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 90 117 9 1 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 90 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 90 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 117 3 2 30 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 117
  (Polychromatic418967fa.accept_19_5_14_3_1_4187 5 90 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 90 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 117 3 1 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 117 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 90 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 117
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 90 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 117)))))))))))))))))))))))))))) (allB_succ' 29 89 117 (Eq.refl Bool.true) (allA_succ_of_accept 28 89 117
  (accept_3_4 28 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 117
  (Polychromatic418967fa.accept_12_3_5_9_1_176 27 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 89 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 89 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 117 (accept_3_4 25 89 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 89 117 (Polychromatic418967fa.accept_15_9_14_12_1_913 24 89 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 117
  (Polychromatic418967fa.accept_19_4_13_3_1_5571 23 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 117 (accept_3_4 22 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 117 (Polychromatic418967fa.accept_25_21_14_17_1_5570 21 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 117 (accept_3_4 19 89 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 117 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 89 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 117
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 117 (accept_3_4 16 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 117 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 89 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 117 (accept_3_4 13 89 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 117 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 89 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 117
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 89 117 (accept_3_4 10 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 89 117 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 89 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 117 (accept_3_4 7 89 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 117 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6
  89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 117
  (Polychromatic418967fa.accept_23_5_20_2_1_5569 5 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 117 (accept_3_4 4 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  117 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 89 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 117 (accept_3_4 1 89 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 117))))))))))))))))))))))))))))) (allB_succ' 30 88 117 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 88 117 (accept_3_5 29 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 117 (Polychromatic418967fa.accept_16_12_8_5_1_3316 28 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 88 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 117 (accept_3_5 26 88 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 117
  (Polychromatic418967fa.accept_21_3_4_12_1_1462 24 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 117 (accept_3_5 23 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 117 (Polychromatic418967fa.accept_19_2_12_3_1_5446 21 88 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 117 (accept_3_5 20 88 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 117
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 117 (accept_3_5 17 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 88 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 117 (accept_3_5 14 88 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 117
  (Polychromatic418967fa.accept_16_12_8_5_1_3316 12 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 117 (accept_3_5 11 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 117 (Polychromatic418967fa.accept_15_10_13_12_1_3384 10 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 88 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 117 (accept_3_5 8 88 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 117
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 117 (accept_3_5 5 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  117 (Polychromatic418967fa.accept_16_4_8_5_1_3317 4 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 88 117 (Polychromatic418967fa.accept_15_3_13_12_1_348 3 88 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 117 (accept_3_5 2 88 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 117)))))))))))))))))))))))))))))) (allB_succ' 31 87
  117 (Eq.refl Bool.true) (allA_succ_of_gcd 30 87 117 3 10 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 87 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 117
  (Polychromatic418967fa.accept_16_12_7_5_1_1412 28 87 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 87 117 3 9 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 87 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 117 (Polychromatic418967fa.accept_11_3_10_7_1_129 25 87 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 87 117 3 8 29 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 87 117
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 87 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 117 3 7 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 117 (Polychromatic418967fa.accept_19_1_11_3_1_5463 20 87 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 117
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 87 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 87 117 3 6 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 87 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 87 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 87 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 87 117 3 5 29 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 87 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 117 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 87 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 117 3 4 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 117 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 87 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 87 117 3 3 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 87 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 87 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 117 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 87 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 117 3 2 29 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 117
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 87 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 117 (Polychromatic418967fa.accept_17_4_2_15_1_1254 4 87 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 117 3 1 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 117
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 87 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 87 117))))))))))))))))))))))))))))))) (allB_succ' 32 86 117 (Eq.refl Bool.true) (allA_succ_of_accept 31 86
  117 (accept_3_4 31 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 86 117
  (Polychromatic418967fa.accept_12_6_2_9_1_537 30 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 86 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 117 (accept_3_4 28 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 86 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 117 (Polychromatic418967fa.accept_17_9_1_15_1_3156
  26 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 86 117 (accept_3_4 25
  86 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 86 117
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 86 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 117 (accept_3_4 22 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 86 117 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 86 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 117 (Polychromatic418967fa.accept_16_4_6_5_1_2245
  20 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 86 117 (accept_3_4 19
  86 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 86 117
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 86 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 117 (accept_3_4 16 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 86 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 117
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 14 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 86 117 (accept_3_4 13 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 86 117 (Polychromatic418967fa.accept_17_12_1_15_1_5472 12 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 86 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 117 (accept_3_4 10 86 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 117 (Polychromatic418967fa.accept_17_9_1_15_1_3156
  9 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 117
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 117 (accept_3_4 7 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  117 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 117 (accept_3_4 4 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 117 (Polychromatic418967fa.accept_11_2_9_7_1_124 2
  86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 117 (accept_3_4 1 86 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86 117)))))))))))))))))))))))))))))))) (allB_succ' 33 85 117
  (Eq.refl Bool.true) (allA_succ_of_accept 32 85 117 (accept_3_5 32 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 85 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 85 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 117 (Polychromatic418967fa.accept_19_11_9_3_1_4167 30 85
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 117 (accept_3_5 29 85 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 28
  85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 117
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 117 (accept_3_5 26 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 117 (accept_3_5 23 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 85 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 117
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 21 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 117 (accept_3_5 20 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 117 (Polychromatic418967fa.accept_21_19_1_12_1_5485 19 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 117 (accept_3_5 17 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 117
  (Polychromatic418967fa.accept_11_4_8_7_1_819 15 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 117 (accept_3_5 14 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 117 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 117 (accept_3_5 11 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 85 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 117
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 117 (accept_3_5 8 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  117 (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 85 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 117 (accept_3_5 5 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 117
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 117 (accept_3_5 2 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85
  117 (Polychromatic418967fa.accept_23_1_16_2_1_5568 1 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 85 117))))))))))))))))))))))))))))))))) (allB_succ' 34 84 117 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 84 117 3 11 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 84 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 84 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 117 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 84 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 117 3 10 28 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 117
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 84 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 117 (Polychromatic418967fa.accept_16_12_4_5_1_2273 28 84 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 84 117 3 9 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 84 117 (Polychromatic418967fa.accept_25_1_9_17_1_5567 26 84 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 117
  (Polychromatic418967fa.accept_8_1_4_5_1_48 25 84 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 117 3 8 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 117 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 84 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 84 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84 117 3 7 28 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 84 117
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 20 84 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 84 117 (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 84 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 117 3 6 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 84 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 117
  (Polychromatic418967fa.accept_18_16_12_9_1_5504 16 84 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 84 117 3 5 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 84 117 (Polychromatic418967fa.accept_15_14_9_12_1_2498 14 84 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 117 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 84 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 117 3 4 28 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 117
  (Polychromatic418967fa.accept_10_1_4_7_1_374 11 84 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 117 (Polychromatic418967fa.accept_15_10_9_12_1_2497 10 84 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 117 3 3 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 117 (Polychromatic418967fa.accept_16_8_4_5_1_4379 8 84 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 117
  (Polychromatic418967fa.accept_20_7_4_17_1_4132 7 84 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 84 117 3 2 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 117 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 84 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 117 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 84 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 84 117 3 1 28 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 84 117
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 84 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 84 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 84 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84 117)))))))))))))))))))))))))))))))))) (allB_succ' 35 83 117 (Eq.refl
  Bool.true) (allA_succ_of_accept 34 83 117 (accept_3_4 34 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 83 117 (Polychromatic418967fa.accept_15_3_8_12_1_900 33 83 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 117 (accept_3_4 31 83 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 117
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 117 (accept_3_4 28 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 117 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 117 (accept_3_4 25 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 117 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 83 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 117
  (Polychromatic418967fa.accept_11_1_6_7_1_116 23 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 117 (accept_3_4 22 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 117 (Polychromatic418967fa.accept_22_21_17_7_1_5566 21 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 117 (accept_3_4 19 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 117
  (Polychromatic418967fa.accept_27_17_2_9_1_5565 17 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 117 (accept_3_4 16 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 117 (accept_3_4 13 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 117 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 83 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 117
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 117 (accept_3_4 10 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 117 (Polychromatic418967fa.accept_21_9_20_12_1_5564 9 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 117 (accept_3_4 7 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 117
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 117 (accept_3_4 4 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  117 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 83 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 117 (accept_3_4 1 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 83 117))))))))))))))))))))))))))))))))))) (allB_succ' 36 82 117 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 82 117 (accept_3_5 35 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 117 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 117 (Polychromatic418967fa.accept_15_3_7_12_1_372 33 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 117 (accept_3_5 32 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 117
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 117 (accept_3_5 29 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 117 (Polychromatic418967fa.accept_19_9_6_3_1_5563 28 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 117 (accept_3_5 26 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 82 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 117
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 117 (accept_3_5 23 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 117 (Polychromatic418967fa.accept_21_1_19_12_1_5562 22 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 117 (Polychromatic418967fa.accept_14_7_12_5_1_1861 21 82 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 117 (accept_3_5 20 82 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 117
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 117 (accept_3_5 17 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 117 (Polychromatic418967fa.accept_17_16_14_15_1_1250 16 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 117 (accept_3_5 14 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 82 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 117
  (Polychromatic418967fa.accept_17_12_14_15_1_5561 12 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 82 117 (accept_3_5 11 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 82 117 (Polychromatic418967fa.accept_14_10_12_5_1_3466 10 82 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 117 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 82 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 117 (accept_3_5 8 82 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 117
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 117 (accept_3_5 5 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  117 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 117 (accept_3_5 2 82 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 117)))))))))))))))))))))))))))))))))))) (allB_succ' 37 81 117
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 81 117 9 4 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 81 117 (Polychromatic418967fa.accept_15_5_6_12_1_916 35 81 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 117
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 81 117 3 11 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 81 117 (Polychromatic418967fa.accept_15_2_6_12_1_1613 32 81 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 117 (Polychromatic418967fa.accept_16_15_1_5_1_2265 31 81
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 117 3 10 27 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 117
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 117 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 81 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 81 117 9 3 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 117 (Polychromatic418967fa.accept_10_6_1_7_1_342 26 81 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 117
  (Polychromatic418967fa.accept_11_3_4_7_1_114 25 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 81 117 3 8 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 81 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 81 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 81 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 117 3 7 27 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 117
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 117 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 81 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 117 9 2 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 117 (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 81 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 117
  (Polychromatic418967fa.accept_7_2_4_5_1_313 16 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 81 117 3 5 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 81 117 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 81 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 81 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 117 3 4 27 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 117
  (Polychromatic418967fa.accept_17_11_13_15_1_2140 11 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 81 117 (Polychromatic418967fa.accept_15_10_6_12_1_1645 10 81 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 117 9 1 9 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 117
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 117 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 81 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 117 3 2 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 117 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 81 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 117
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 81 117 3 1 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 81 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 81 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 81 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 117)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 80 117 (Eq.refl Bool.true) (allA_succ_of_accept 37 80 117 (accept_3_4 37 80 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 80 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 80 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 80 117
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 80 117 (accept_3_4 34 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  80 117 (Polychromatic418967fa.accept_26_7_2_13_1_5560 33 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 80 117 (Polychromatic418967fa.accept_11_10_3_7_1_2564 32 80 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 80 117 (accept_3_4 31 80 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 80 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 80 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 80 117
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 80 117 (accept_3_4 28 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  80 117 (Polychromatic418967fa.accept_19_8_4_3_1_5559 27 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 80 117 (Polychromatic418967fa.accept_11_4_3_7_1_828 26 80 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 80 117 (accept_3_4 25 80 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 80 117 (Polychromatic418967fa.accept_15_9_5_12_1_1640 24 80 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 80 117
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 80 117 (accept_3_4 22 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  80 117 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 80 117 (Polychromatic418967fa.accept_17_3_12_15_1_1203 20 80 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 80 117 (accept_3_4 19 80 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 117 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 80 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 80 117
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 80 117 (accept_3_4 16 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  80 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 80 117 (Polychromatic418967fa.accept_17_14_12_15_1_5558 14 80 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 80 117 (accept_3_4 13 80 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 80 117 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 80
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 117
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 80 117 (accept_3_4 10 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  80 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 80 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 80 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 117 (accept_3_4 7 80 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 117 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 80 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 80 117
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 80 117 (accept_3_4 4 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80
  117 (Polychromatic418967fa.accept_17_3_12_15_1_1203 3 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 80 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 80 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 117 (accept_3_4 1 80 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 80 117)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 79 117 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 79 117 (accept_3_5 38 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 117 (Polychromatic418967fa.accept_15_7_4_12_1_2530 37 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 117 (Polychromatic418967fa.accept_16_4_15_5_1_5537 36 79 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 117 (accept_3_5 35 79 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 117
  (Polychromatic418967fa.accept_16_1_15_5_1_708 33 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 117 (accept_3_5 32 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 117 (accept_3_5 29 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 117
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 117 (accept_3_5 26 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 117 (accept_3_5 23 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 117
  (Polychromatic418967fa.accept_14_7_9_5_1_529 21 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 117 (accept_3_5 20 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 117 (Polychromatic418967fa.accept_22_19_13_7_1_5557 19 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 117 (accept_3_5 17 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 117
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 117 (accept_3_5 14 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 117 (Polychromatic418967fa.accept_17_13_11_15_1_5556 13 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 117 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 117 (accept_3_5 11 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 117
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 117 (accept_3_5 8 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  117 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 79 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 117 (accept_3_5 5 79 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 79 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 117 (accept_3_5 2 79 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 117 (Polychromatic418967fa.accept_15_1_4_12_1_2401
  1 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  117))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 78 117 (Eq.refl Bool.true) (allA_succ_of_gcd 39 78 117 39 1
  2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 117
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 78 117 (Polychromatic418967fa.accept_15_7_3_12_1_365 37 78 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 117 3 12 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 117
  (Polychromatic418967fa.accept_7_6_1_5_1_322 34 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 78 117 3 11 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 78 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 78 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 117 3 10 26 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 117
  (Polychromatic418967fa.accept_10_9_8_7_1_714 29 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 117 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 78 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 117 3 9 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 78 117 13 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 78 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 117 3 8 26 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 117 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 78 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 117 3 7 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 78 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 117 3 6 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 78 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 117 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 78 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 78 117 3 5 26 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 78 117
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 78 117 13 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 78 117 3 4 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 78 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 117 3 3 26 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 117
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 78 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 117 3 2 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 117 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 78 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 117
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 78 117 3 1 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 78 117 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 78 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 117 (Polychromatic418967fa.accept_18_1_6_9_1_2001 1 78 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 117))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 77 117 (Eq.refl Bool.true) (allA_succ_of_accept 40 77 117 (accept_3_4 40 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 77 117 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 77 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 117
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 77 117 (accept_3_4 37 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  77 117 (Polychromatic418967fa.accept_15_6_2_12_1_885 36 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 77 117 (Polychromatic418967fa.accept_15_5_2_12_1_2543 35 77 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 77 117 (accept_3_4 34 77 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 77 117 (Polychromatic418967fa.accept_15_3_2_12_1_2469 33 77
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 117
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 77 117 (accept_3_4 31 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  77 117 (Polychromatic418967fa.accept_14_2_7_5_1_5450 30 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 77 117 (Polychromatic418967fa.accept_15_14_2_12_1_2472 29 77 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 117 (accept_3_4 28 77 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 77 117 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 77 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 117
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 117 (accept_3_4 25 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 117 (Polychromatic418967fa.accept_16_8_13_5_1_1395 24 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 117 (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 117 (accept_3_4 22 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 77 117 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 77 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 117
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 117 (accept_3_4 19 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 117 (Polychromatic418967fa.accept_15_3_2_12_1_2469 18 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 117 (Polychromatic418967fa.accept_16_1_13_5_1_2280 17 77 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 117 (accept_3_4 16 77 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 117 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 77 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 117
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 117 (accept_3_4 13 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 117 (Polychromatic418967fa.accept_14_12_7_5_1_1107 12 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 77 117 (Polychromatic418967fa.accept_19_11_1_3_1_5555 11 77 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 117 (accept_3_4 10 77 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 117 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 77 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 117
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 117 (accept_3_4 7 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77
  117 (Polychromatic418967fa.accept_15_6_2_12_1_885 6 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 77 117 (Polychromatic418967fa.accept_15_5_2_12_1_2543 5 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 117 (accept_3_4 4 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 117 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 77 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 117
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 117 (accept_3_4 1 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  117))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 76 117 (Eq.refl Bool.true) (allA_succ_of_accept 41 76 117
  (accept_3_5 41 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 117
  (Polychromatic418967fa.accept_16_8_12_5_1_200 40 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 76 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 117 (accept_3_5 38 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 76 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 36
  76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 117 (accept_3_5 35 76
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 117
  (Polychromatic418967fa.accept_15_4_1_12_1_914 34 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 76 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 117 (accept_3_5 32 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 76 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 117 (Polychromatic418967fa.accept_12_6_4_9_1_544
  30 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 117 (accept_3_5 29
  76 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 117
  (Polychromatic418967fa.accept_15_13_1_12_1_1638 28 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 76 117 (Polychromatic418967fa.accept_14_13_6_5_1_1853 27 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 117 (accept_3_5 26 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 76 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 117 (Polychromatic418967fa.accept_16_8_12_5_1_200
  24 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 117 (accept_3_5 23
  76 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 117
  (Polychromatic418967fa.accept_7_1_6_5_1_39 22 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 76 117 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 117 (accept_3_5 20 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 76 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 18
  76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 117 (accept_3_5 17 76
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 117
  (Polychromatic418967fa.accept_22_16_10_7_1_5554 16 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 76 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 117 (accept_3_5 14 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 76 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 117 (Polychromatic418967fa.accept_18_12_4_9_1_5452
  12 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 117 (accept_3_5 11
  76 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 117
  (Polychromatic418967fa.accept_16_10_12_5_1_2254 10 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 76 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 117 (accept_3_5 8 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 76 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 117 (Polychromatic418967fa.accept_12_6_4_9_1_544 6
  76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 117 (accept_3_5 5 76 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 4
  76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 117
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 76 117 (accept_3_5 2 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76
  117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 117)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 75 117 (Eq.refl Bool.true) (allA_succ_of_gcd
  42 75 117 3 14 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 75 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 75 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 117 (Polychromatic418967fa.accept_16_8_11_5_1_3319 40 75
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 75 117 3 13 25 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 75 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 117 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 75 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 117 3 12 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 117 (Polychromatic418967fa.accept_11_2_9_7_1_124 35
  75 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 75 117 3 11 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 75 117 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 75 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 117 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 75 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 117 3 10 25 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 117
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 75 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 75 117 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 75 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 117 3 9 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 117
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 75 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 75 117 3 8 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 75 117 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 75 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 117 3 7 25 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 75 117
  (Polychromatic418967fa.accept_18_2_3_9_1_1996 20 75 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 117 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 75 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 117 3 6 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 75 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 117
  (Polychromatic418967fa.accept_11_5_9_7_1_411 16 75 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 75 117 3 5 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 75 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 117 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 75 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 117 3 4 25 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 117
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 75 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 117 3 3 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 117 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 75 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 117
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 75 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 75 117 3 2 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 75 117 (Polychromatic418967fa.accept_11_5_9_7_1_411 5 75 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 117 (Polychromatic418967fa.accept_19_4_18_3_1_5553 4 75 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 117 3 1 25 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 117 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 75 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 75 117))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 74 117
  (Eq.refl Bool.true) (allA_succ_of_accept 43 74 117 (accept_3_4 43 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 74 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 74 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 74 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 117 (accept_3_4 40 74 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 117
  (Polychromatic418967fa.accept_22_16_8_7_1_5552 38 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 117 (accept_3_4 37 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 117 (accept_3_4 34 74 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 117 (Polychromatic418967fa.accept_10_3_4_7_1_353 33 74 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 117
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 117 (accept_3_4 31 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 74 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 117 (accept_3_4 28 74 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 117
  (Polychromatic418967fa.accept_11_4_8_7_1_819 26 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 117 (accept_3_4 25 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 117 (Polychromatic418967fa.accept_15_9_14_12_1_913 24 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 117 (accept_3_4 22 74 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 117 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 74 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 117
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 117 (accept_3_4 19 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 117 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 74 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 117 (accept_3_4 16 74 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 117
  (Polychromatic418967fa.accept_16_14_10_5_1_1393 14 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 117 (accept_3_4 13 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 117 (accept_3_4 10 74 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 74 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 117
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 117 (accept_3_4 7 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  117 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 117 (accept_3_4 4 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 117 (accept_3_4 1 74 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74 117)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45
  73 117 (Eq.refl Bool.true) (allA_succ_of_accept 44 73 117 (accept_3_5 44 73 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 73 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 73 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 117 (Polychromatic418967fa.accept_18_6_1_9_1_5551
  42 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 117 (accept_3_5 41
  73 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 73 117
  (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 73 117 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 73 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 117 (accept_3_5 38 73 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 73 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 73 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 36
  73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 73 117 (accept_3_5 35 73
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 73 117 (Polychromatic418967fa.accept_6_4_1_3_1_77
  34 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 73 117
  (Polychromatic418967fa.accept_15_3_13_12_1_348 33 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 73 117 (accept_3_5 32 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  73 117 (Polychromatic418967fa.accept_15_1_13_12_1_347 31 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 73 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 73 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 117 (accept_3_5 29 73 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 73 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 117
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 73 117 (accept_3_5 26 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  73 117 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 73 117 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 73 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 117 (accept_3_5 23 73 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 73 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 117
  (Polychromatic418967fa.accept_18_3_1_9_1_1929 21 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 73 117 (accept_3_5 20 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  73 117 (Polychromatic418967fa.accept_21_19_10_12_1_5550 19 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 73 117 (Polychromatic418967fa.accept_15_3_13_12_1_348 18 73 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 117 (accept_3_5 17 73 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 117
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 117 (accept_3_5 14 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 117 (Polychromatic418967fa.accept_16_13_9_5_1_3302 13 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 117 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 73 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 117 (accept_3_5 11 73 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 73 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 117
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 117 (accept_3_5 8 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  117 (Polychromatic418967fa.accept_17_7_5_15_1_3184 7 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 73 117 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 73 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 117 (accept_3_5 5 73 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 73 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 117
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 73 117 (accept_3_5 2 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73
  117 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 73 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 73 117))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 72 117 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 72 117 9 5 8 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 117 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 72 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 117 (Polychromatic418967fa.accept_16_11_8_5_1_4366 43 72
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 117 3 14 24 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 117
  (Polychromatic418967fa.accept_21_20_9_12_1_5549 41 72 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 117 (Polychromatic418967fa.accept_21_19_9_12_1_4071 40 72 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 117 3 13 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 38
  72 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 117
  (Polychromatic418967fa.accept_19_18_15_3_1_5548 37 72 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 117 9 4 8 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 117 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 72 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 117 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 72 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 117 3 11 24 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 117
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 72 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 72 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 117 3 10 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 117 (Polychromatic418967fa.accept_10_9_2_7_1_1096
  29 72 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 117
  (Polychromatic418967fa.accept_16_12_8_5_1_3316 28 72 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 117 9 3 8 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 117 (Polychromatic418967fa.accept_19_7_15_3_1_2896 26 72 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 72 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 117 3 8 24 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 117
  (Polychromatic418967fa.accept_11_1_6_7_1_116 23 72 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 117 (Polychromatic418967fa.accept_20_2_12_17_1_5547 22 72 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 117 3 7 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 117 (Polychromatic418967fa.accept_16_4_8_5_1_3317 20 72 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 117
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 72 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 117 9 2 8 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 72 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 117 (Polychromatic418967fa.accept_17_16_4_15_1_4342 16 72
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 117 3 5 24 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 117
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 72 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 117 (Polychromatic418967fa.accept_16_13_8_5_1_3298 13 72 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 117 3 4 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 72 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 117
  (Polychromatic418967fa.accept_7_3_2_5_1_147 10 72 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 72 117 9 1 8 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 72 117 (Polychromatic418967fa.accept_19_8_15_3_1_5546 8 72 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 117 (Polychromatic418967fa.accept_14_7_2_5_1_4528 7 72 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 117 3 2 24 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 117
  (Polychromatic418967fa.accept_10_5_2_7_1_345 5 72 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 72 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 117 3 1 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 117 (Polychromatic418967fa.accept_17_2_4_15_1_5451 2 72 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 117
  (Polychromatic418967fa.accept_11_1_6_7_1_116 1 72 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 117)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 71 117 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 71 117 (accept_3_4 46 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 117 (accept_3_4 43 71 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 117
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 117 (accept_3_4 40 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 117 (accept_3_4 37 71 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 117 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 71 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 117
  (Polychromatic418967fa.accept_17_1_3_15_1_2153 35 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 117 (accept_3_4 34 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 117 (Polychromatic418967fa.accept_18_15_17_9_1_4200 33 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 117 (accept_3_4 31 71 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 117
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 29 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 71 117 (accept_3_4 28 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 71 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 71 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 117 (accept_3_4 25 71 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 24
  71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 117
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 23 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 117 (accept_3_4 22 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 117 (Polychromatic418967fa.accept_20_1_11_17_1_1639 21 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 117 (accept_3_4 19 71 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 117
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 117 (accept_3_4 16 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 117 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 117 (accept_3_4 13 71 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 117 (Polychromatic418967fa.accept_16_12_7_5_1_1412 12 71 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 117
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 117 (accept_3_4 10 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 117 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 117 (accept_3_4 7 71 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 117
  (Polychromatic418967fa.accept_19_5_14_3_1_4187 5 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 117 (accept_3_4 4 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  117 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 71 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 117 (accept_3_4 1 71 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 117))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 70 117 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 70 117 (accept_3_5 47 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  70 117 (Polychromatic418967fa.accept_19_8_13_3_1_4172 46 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 70 117 (Polychromatic418967fa.accept_19_7_13_3_1_4171 45 70 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 70 117 (accept_3_5 44 70 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 117
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 70 117 (accept_3_5 41 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  70 117 (Polychromatic418967fa.accept_21_19_7_12_1_5507 40 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 70 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 117 (accept_3_5 38 70 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 70 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 70 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 117
  (Polychromatic418967fa.accept_11_3_4_7_1_114 36 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 70 117 (accept_3_5 35 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  70 117 (Polychromatic418967fa.accept_25_9_20_17_1_5545 34 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 70 117 (Polychromatic418967fa.accept_16_1_6_5_1_4385 33 70 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 117 (accept_3_5 32 70 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 117
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 70 117 (accept_3_5 29 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  70 117 (Polychromatic418967fa.accept_15_13_10_12_1_2503 28 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 70 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 117 (accept_3_5 26 70 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 70 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 70 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 117
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 70 117 (accept_3_5 23 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  70 117 (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 70 117 (Polychromatic418967fa.accept_15_6_10_12_1_2538 21 70 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 70 117 (accept_3_5 20 70 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 117
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 117 (accept_3_5 17 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  70 117 (Polychromatic418967fa.accept_19_16_13_3_1_5544 16 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 70 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 117 (accept_3_5 14 70 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 70 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 117
  (Polychromatic418967fa.accept_18_12_16_9_1_4198 12 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 117 (accept_3_5 11 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  70 117 (Polychromatic418967fa.accept_17_10_2_15_1_3179 10 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 70 117 (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 70 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 117 (accept_3_5 8 70 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 117
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 70 117 (accept_3_5 5 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70
  117 (Polychromatic418967fa.accept_16_4_6_5_1_2245 4 70 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 70 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 117 (accept_3_5 2 70 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 70 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70 117))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 69 117 (Eq.refl Bool.true) (allA_succ_of_gcd 48 69 117 3 16 23 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 117
  (Polychromatic418967fa.accept_18_11_15_9_1_360 47 69 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 69 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 117 3 15 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 117 (Polychromatic418967fa.accept_15_14_9_12_1_2498
  44 69 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 117
  (Polychromatic418967fa.accept_7_1_6_5_1_39 43 69 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 117 3 14 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 117 (Polychromatic418967fa.accept_18_5_15_9_1_1919 41 69 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 117 (Polychromatic418967fa.accept_15_10_9_12_1_2497 40 69
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 117 3 13 23 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 117
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 38 69 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 117 (Polychromatic418967fa.accept_11_4_3_7_1_828 37 69 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 117 3 12 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 117 (Polychromatic418967fa.accept_15_5_9_12_1_1599
  35 69 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 117
  (Polychromatic418967fa.accept_14_6_13_5_1_534 34 69 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 117 3 11 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 69 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 117 (Polychromatic418967fa.accept_21_10_6_12_1_5543 31 69
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 117 3 10 23 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 117
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 69 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 117 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 69 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 117 3 9 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 117 (Polychromatic418967fa.accept_11_4_3_7_1_828 26 69 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 117
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 69 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 117 3 8 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 117 (Polychromatic418967fa.accept_18_5_15_9_1_1919 23 69 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 69 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 117 3 7 23 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 117
  (Polychromatic418967fa.accept_14_6_13_5_1_534 20 69 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 117 (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 69 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 117 3 6 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 117 (Polychromatic418967fa.accept_18_17_15_9_1_5542 17 69
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 117
  (Polychromatic418967fa.accept_17_16_1_15_1_5541 16 69 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 117 3 5 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 117 (Polychromatic418967fa.accept_15_14_9_12_1_2498 14 69 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 117 (Polychromatic418967fa.accept_19_13_12_3_1_5540 13 69
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 117 3 4 23 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 117
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 69 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 117 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 69 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 117 3 3 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 69 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 117
  (Polychromatic418967fa.accept_19_7_12_3_1_4169 7 69 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 117 3 2 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 117 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 69 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 69 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 117 3 1 23 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 117
  (Polychromatic418967fa.accept_10_2_9_7_1_720 2 69 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 69 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 117))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 68
  117 (Eq.refl Bool.true) (allA_succ_of_accept 49 68 117 (accept_3_4 49 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 68 117 (Polychromatic418967fa.accept_15_3_8_12_1_900 48 68 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 68 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 117 (accept_3_4 46 68 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 117 (Polychromatic418967fa.accept_10_5_8_7_1_2174
  45 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 117
  (Polychromatic418967fa.accept_16_12_4_5_1_2273 44 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 117 (accept_3_4 43 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 117 (Polychromatic418967fa.accept_11_9_2_7_1_1298 42 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 117 (accept_3_4 40 68 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 117 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 68 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 117
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 38 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 117 (accept_3_4 37 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 117 (Polychromatic418967fa.accept_21_15_5_12_1_3987 36 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 117 (accept_3_4 34 68 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 68 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 117
  (Polychromatic418967fa.accept_19_13_11_3_1_5465 32 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 117 (accept_3_4 31 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 117 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 117 (accept_3_4 28 68 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 117 (Polychromatic418967fa.accept_19_8_11_3_1_5539 27 68 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 117
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 26 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 117 (accept_3_4 25 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 117 (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 117 (accept_3_4 22 68 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 117 (Polychromatic418967fa.accept_14_7_12_5_1_1861 21 68 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 117
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 117 (accept_3_4 19 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 117 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 117 (accept_3_4 16 68 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 117 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 68 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 117
  (Polychromatic418967fa.accept_19_14_11_3_1_5508 14 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 117 (accept_3_4 13 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 117 (Polychromatic418967fa.accept_16_12_4_5_1_2273 12 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 117 (accept_3_4 10 68 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 68 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 117
  (Polychromatic418967fa.accept_16_8_4_5_1_4379 8 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 117 (accept_3_4 7 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  117 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 117 (accept_3_4 4 68 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 117 (Polychromatic418967fa.accept_14_3_12_5_1_153 3 68 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 117 (Polychromatic418967fa.accept_19_2_11_3_1_4136
  2 68 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 117 (accept_3_4 1 68
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68 117))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 67 117 (Eq.refl Bool.true) (allA_succ_of_accept 50 67 117 (accept_3_5 50 67 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 117 (Polychromatic418967fa.accept_15_4_7_12_1_5538 49 67 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 117
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 117 (accept_3_5 47 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 117 (Polychromatic418967fa.accept_17_11_16_15_1_5467 45 67 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 117 (accept_3_5 44 67 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 67 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 117 (accept_3_5 41 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 117 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 67 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 117 (accept_3_5 38 67 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 67 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 117
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 117 (accept_3_5 35 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 117 (Polychromatic418967fa.accept_15_3_7_12_1_372 33 67 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 117 (accept_3_5 32 67 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 117 (Polychromatic418967fa.accept_17_14_16_15_1_5509 31 67 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 117 (accept_3_5 29 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 67 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 117 (accept_3_5 26 67 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 117 (Polychromatic418967fa.accept_15_10_7_12_1_2490 25 67 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 117
  (Polychromatic418967fa.accept_16_8_3_5_1_5512 24 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 117 (accept_3_5 23 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 117 (Polychromatic418967fa.accept_15_6_7_12_1_869 21 67 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 117 (accept_3_5 20 67 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 117 (Polychromatic418967fa.accept_15_4_7_12_1_5538 19 67 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 117 (accept_3_5 17 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 67 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 117 (accept_3_5 14 67 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 67 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 117
  (Polychromatic418967fa.accept_19_12_10_3_1_5503 12 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 117 (accept_3_5 11 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 67 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 117 (accept_3_5 8 67 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 117 (Polychromatic418967fa.accept_19_7_10_3_1_4149 7 67 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 117 (accept_3_5 5 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 117 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 67 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 117 (accept_3_5 2 67 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 67 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 117)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 66 117 (Eq.refl Bool.true) (allA_succ_of_gcd 51 66 117 3 17 22 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 66 117
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 66 117 (Polychromatic418967fa.accept_19_11_9_3_1_4167 49 66 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 117 3 16 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 117
  (Polychromatic418967fa.accept_12_10_6_9_1_549 46 66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 66 117 3 15 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 66 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 66 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 117 3 14 22 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 117
  (Polychromatic418967fa.accept_10_1_6_7_1_710 41 66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 117 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 66 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 66 117 3 13 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 66 117 (Polychromatic418967fa.accept_12_2_6_9_1_19 38
  66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 117
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 117 3 12 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 117 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 66 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 66 117 3 11 22 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 66 117
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 66 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 117 3 10 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 29
  66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 117
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 66 117 3 9 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 66 117 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 66 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 117 (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 66
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 117 3 8 22 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 66 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 66 117 3 7 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 117 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 66 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 117 3 6 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 117 (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 66 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 66 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 66 117 3 5 22 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 66 117
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 66 117 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 66 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 117 3 4 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 117
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 66 117 3 3 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 66 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 66 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 117 3 2 22 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 117
  (Polychromatic418967fa.accept_15_5_6_12_1_916 5 66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 117 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 66 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 117 3 1 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 66 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 117
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 66 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 117)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 65 117 (Eq.refl Bool.true)
  (allA_succ_of_gcd 52 65 117 13 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 65 117 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 65 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 65 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 117 (accept_3_4 49 65 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 117 (Polychromatic418967fa.accept_10_8_5_7_1_358
  48 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 117
  (Polychromatic418967fa.accept_11_3_10_7_1_129 47 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 117 (accept_3_4 46 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 117 (accept_3_4 43 65 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 117 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 65 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 117
  (Polychromatic418967fa.accept_16_9_1_5_1_2282 41 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 117 (accept_3_4 40 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 65
  117 13 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38
  65 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 65 117 (accept_3_4 37 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 65 117 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 65 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 117 (Polychromatic418967fa.accept_14_7_9_5_1_529 35 65 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 117 (accept_3_4 34 65 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 117 (Polychromatic418967fa.accept_10_3_5_7_1_330
  33 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 117
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 117 (accept_3_4 31 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 117 (Polychromatic418967fa.accept_18_12_11_9_1_4257 30 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 117 (Polychromatic418967fa.accept_16_13_1_5_1_5469 29 65 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 117 (accept_3_4 28 65 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 117 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 65 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 65 117 13 2 5 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 65 117 (accept_3_4 25 65 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 24
  65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 117
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 117 (accept_3_4 22 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 117 (Polychromatic418967fa.accept_14_7_9_5_1_529 21 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 117 (accept_3_4 19 65 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 65 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 117
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 117 (accept_3_4 16 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 117 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 65 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 65 117 13 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 65 117 (Polychromatic418967fa.accept_8_4_1_5_1_186 12
  65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 117
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 117 (accept_3_4 10 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 117 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 117 (accept_3_4 7 65 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 117 (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 65 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 117
  (Polychromatic418967fa.accept_19_5_8_3_1_5498 5 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 117 (accept_3_4 4 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  117 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 65 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 65 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 117 (accept_3_4 1 65 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 117))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 64 117 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 64 117 (accept_3_5 53 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 64 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 64 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 117 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 64 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 117 (accept_3_5 50 64 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 64 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 49
  64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 117
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 64 117 (accept_3_5 47 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  64 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 64 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 64 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 117 (accept_3_5 44 64 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 64 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 117
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 64 117 (accept_3_5 41 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  64 117 (Polychromatic418967fa.accept_21_19_1_12_1_5485 40 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 64 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 64 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 117 (accept_3_5 38 64 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 64 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 117
  (Polychromatic418967fa.accept_17_2_13_15_1_4349 36 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 64 117 (accept_3_5 35 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  64 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 64 117 (Polychromatic418967fa.accept_10_3_4_7_1_353 33 64 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 117 (accept_3_5 32 64 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 64 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 117
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 64 117 (accept_3_5 29 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  64 117 (Polychromatic418967fa.accept_17_11_13_15_1_2140 28 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 64 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 64 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 117 (accept_3_5 26 64 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 64 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 117
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 64 117 (accept_3_5 23 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  64 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 64 117 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 64 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 117 (accept_3_5 20 64 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 64 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 117
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 64 117 (accept_3_5 17 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  64 117 (Polychromatic418967fa.accept_11_5_9_7_1_411 16 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 64 117 (Polychromatic418967fa.accept_18_15_10_9_1_2009 15 64 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 117 (accept_3_5 14 64 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 117
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 117 (accept_3_5 11 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  64 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 117 (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 64 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 117 (accept_3_5 8 64 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 117
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 117 (accept_3_5 5 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64
  117 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 64 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 64 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 64 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 117 (accept_3_5 2 64 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 64 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64 117))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 63 117 (Eq.refl Bool.true) (allA_succ_of_gcd 54 63 117 9 6 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 53
  63 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 117
  (Polychromatic418967fa.accept_15_7_3_12_1_365 52 63 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 63 117 3 17 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 63 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 117 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 63 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 63 117 3 16 21 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 117
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 63 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 117 9 5 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 117 (Polychromatic418967fa.accept_10_4_3_7_1_1110 44 63 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 117
  (Polychromatic418967fa.accept_12_7_3_9_1_999 43 63 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 63 117 3 14 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 63 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 63 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 117 (Polychromatic418967fa.accept_14_12_7_5_1_1107 40 63
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 117 3 13 21 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 117 (Polychromatic418967fa.accept_11_4_8_7_1_819 37 63 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 117 9 4 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 117 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 63 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 63 117 3 11 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 63 117 (Polychromatic418967fa.accept_15_2_3_12_1_891 32 63 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 117 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 63 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 117 3 10 21 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 117
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 63 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 63 117 (Polychromatic418967fa.accept_15_13_3_12_1_1609 28 63 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 117 9 3 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 117
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 63 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 63 117 3 8 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 63 117 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 63 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 117 3 7 21 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 117
  (Polychromatic418967fa.accept_16_4_15_5_1_5537 20 63 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 117 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 63 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 117 9 2 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 63 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 117
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 63 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 63 117 3 5 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 63 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 117 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 63 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 117 3 4 21 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 117
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 63 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 117 9 1 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 117 (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 63 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 117
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 63 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 63 117 3 2 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 63 117 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 63 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 117 (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 63 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 117 3 1 21 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 117 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 63 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 63 117))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56
  62 117 (Eq.refl Bool.true) (allA_succ_of_accept 55 62 117 (accept_3_4 55 62 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 62 117 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 62 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 53
  62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 117 (accept_3_4 52 62
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 62 117 (Polychromatic418967fa.accept_4_3_2_1_1_50
  51 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 117
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 117 (accept_3_4 49 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 117 (Polychromatic418967fa.accept_15_3_2_12_1_2469 48 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 117 (accept_3_4 46 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 117 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 62 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 117
  (Polychromatic418967fa.accept_10_4_2_7_1_373 44 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 117 (accept_3_4 43 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 117 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 117 (accept_3_4 40 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 117
  (Polychromatic418967fa.accept_17_4_11_15_1_3170 38 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 117 (accept_3_4 37 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 117 (accept_3_4 34 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 117 (Polychromatic418967fa.accept_15_3_2_12_1_2469 33 62 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 117
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 117 (accept_3_4 31 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 117 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 117 (accept_3_4 28 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 117
  (Polychromatic418967fa.accept_16_10_14_5_1_5496 26 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 117 (accept_3_4 25 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 117 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 117 (accept_3_4 22 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 117 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 62 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 117
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 20 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 117 (accept_3_4 19 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 117 (accept_3_4 16 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 117
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 117 (accept_3_4 13 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 117 (Polychromatic418967fa.accept_20_12_2_17_1_1620 12 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 117 (accept_3_4 10 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 117 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 62 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 117
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 117 (accept_3_4 7 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  117 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 62 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 117 (accept_3_4 4 62 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 117 (Polychromatic418967fa.accept_19_2_5_3_1_5536 2
  62 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 117 (accept_3_4 1 62 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62 117))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 61 117 (Eq.refl Bool.true) (allA_succ_of_accept 56 61 117 (accept_3_5 56 61 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 117 (Polychromatic418967fa.accept_17_4_10_15_1_5444 55 61 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 117
  (Polychromatic418967fa.accept_10_4_1_7_1_371 54 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 117 (accept_3_5 53 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 117 (Polychromatic418967fa.accept_12_3_1_9_1_202 51 61 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 117 (accept_3_5 50 61 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 117 (Polychromatic418967fa.accept_15_4_1_12_1_914 49 61 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 117
  (Polychromatic418967fa.accept_21_6_19_12_1_3981 48 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 117 (accept_3_5 47 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 117 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 61 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 117 (accept_3_5 44 61 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 117 (Polychromatic418967fa.accept_15_13_1_12_1_1638 43 61 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 117
  (Polychromatic418967fa.accept_16_10_13_5_1_3292 42 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 117 (accept_3_5 41 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 117 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 61 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 117 (accept_3_5 38 61 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 117 (Polychromatic418967fa.accept_19_18_4_3_1_4140 37 61 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 117
  (Polychromatic418967fa.accept_10_6_1_7_1_342 36 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 117 (accept_3_5 35 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 117 (Polychromatic418967fa.accept_16_1_13_5_1_2280 33 61 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 117 (accept_3_5 32 61 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 117 (Polychromatic418967fa.accept_20_11_1_17_1_5535 31 61
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 117
  (Polychromatic418967fa.accept_19_11_4_3_1_5534 30 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 117 (accept_3_5 29 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 117 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 61 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 117 (accept_3_5 26 61 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 117 (Polychromatic418967fa.accept_16_9_13_5_1_2238 25 61 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 117
  (Polychromatic418967fa.accept_10_4_1_7_1_371 24 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 117 (accept_3_5 23 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 117 (Polychromatic418967fa.accept_17_4_10_15_1_5444 21 61 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 117 (accept_3_5 20 61 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 117 (Polychromatic418967fa.accept_15_4_1_12_1_914 19 61 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 117
  (Polychromatic418967fa.accept_16_2_13_5_1_2257 18 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 117 (accept_3_5 17 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 117 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 61 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 117 (accept_3_5 14 61 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 117 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 61 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 117
  (Polychromatic418967fa.accept_11_1_6_7_1_116 12 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 117 (accept_3_5 11 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 117 (Polychromatic418967fa.accept_16_9_13_5_1_2238 9 61 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 117 (accept_3_5 8 61 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 117 (Polychromatic418967fa.accept_19_7_4_3_1_5533 7 61 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 117
  (Polychromatic418967fa.accept_10_6_1_7_1_342 6 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 117 (accept_3_5 5 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 117 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 61 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 117 (accept_3_5 2 61 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 117 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 61 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 117)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 58 60 117 (Eq.refl Bool.true) (allA_succ_of_gcd 57 60 117 3 19 20 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 60 117
  (Polychromatic418967fa.accept_16_8_12_5_1_200 56 60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 60 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 60 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 117 3 18 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 117 (Polychromatic418967fa.accept_11_9_5_7_1_815 53
  60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 117
  (Polychromatic418967fa.accept_16_4_12_5_1_2287 52 60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 60 117 3 17 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 60 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 60 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 60 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 117 3 16 20 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 117
  (Polychromatic418967fa.accept_21_5_18_12_1_5531 47 60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 117 (Polychromatic418967fa.accept_21_4_18_12_1_5532 46 60 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 117 3 15 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 44
  60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 117
  (Polychromatic418967fa.accept_7_1_4_5_1_35 43 60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 117 3 14 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 60 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 117 (Polychromatic418967fa.accept_16_8_12_5_1_200 40 60 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 60 117 3 13 20 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 60 117
  (Polychromatic418967fa.accept_18_2_6_9_1_1032 38 60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 60 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 60 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 117 3 12 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 117 (Polychromatic418967fa.accept_17_1_9_15_1_3186
  35 60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 117
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 60 117 3 11 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 60 117 (Polychromatic418967fa.accept_18_14_6_9_1_1950 32 60 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 117 (Polychromatic418967fa.accept_11_9_5_7_1_815 31 60 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 117 3 10 20 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 117
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 117 (Polychromatic418967fa.accept_21_7_18_12_1_1493 28 60 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 117 3 9 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 117 (Polychromatic418967fa.accept_16_10_12_5_1_2254 26 60
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 117
  (Polychromatic418967fa.accept_8_1_4_5_1_48 25 60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 117 3 8 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 60 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 60 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 60 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 117 3 7 20 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 60 117
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 60 117 (Polychromatic418967fa.accept_18_1_6_9_1_2001 19 60 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 117 3 6 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 60 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 117
  (Polychromatic418967fa.accept_7_2_4_5_1_313 16 60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 60 117 3 5 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 60 117 (Polychromatic418967fa.accept_18_14_6_9_1_1950 14 60 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 60 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 117 3 4 20 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 117
  (Polychromatic418967fa.accept_21_11_18_12_1_1494 11 60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 60 117 (Polychromatic418967fa.accept_16_10_12_5_1_2254 10 60 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 60 117 3 3 20 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 117
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 117 (Polychromatic418967fa.accept_16_7_12_5_1_734 7 60 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 117 3 2 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 117 (Polychromatic418967fa.accept_21_5_18_12_1_5531 5 60 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 117
  (Polychromatic418967fa.accept_16_4_12_5_1_2287 4 60 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 60 117 3 1 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 60 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 60 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 60 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  117)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 117 (allA_succ_of_accept 58 59 117
  (accept_3_4 58 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 117
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 117 (accept_3_4 55 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 117 (Polychromatic418967fa.accept_22_9_15_7_1_2581
  53 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 117 (accept_3_4 52
  59 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 117
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 59 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 117 (accept_3_4 49 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 59 117 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 59 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 117 (Polychromatic418967fa.accept_11_3_4_7_1_114
  47 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 117 (accept_3_4 46
  59 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 117
  (Polychromatic418967fa.accept_21_3_17_12_1_5530 45 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 59 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 117 (accept_3_4 43 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 59 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 117 (Polychromatic418967fa.accept_11_8_4_7_1_1303
  41 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 117 (accept_3_4 40
  59 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 117
  (Polychromatic418967fa.accept_12_3_11_9_1_193 39 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 59 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 117 (accept_3_4 37 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 59 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 59 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 117 (Polychromatic418967fa.accept_19_16_2_3_1_5479
  35 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 117 (accept_3_4 34
  59 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 117
  (Polychromatic418967fa.accept_18_15_5_9_1_5529 33 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 59 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 117 (accept_3_4 31 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 59 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 29
  59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 117 (accept_3_4 28 59
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 117
  (Polychromatic418967fa.accept_12_3_11_9_1_193 27 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 59 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 117 (accept_3_4 25 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 59 117 (Polychromatic418967fa.accept_15_9_14_12_1_913 24 59 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 117
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 117 (accept_3_4 22 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 117 (Polychromatic418967fa.accept_23_21_13_2_1_5528 21 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 117 (accept_3_4 19 59 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 117
  (Polychromatic418967fa.accept_15_2_14_12_1_2453 17 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 117 (accept_3_4 16 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 117 (accept_3_4 13 59 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 117 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 59 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 117
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 59 117 (accept_3_4 10 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 59 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 117 (accept_3_4 7 59 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 117
  (Polychromatic418967fa.accept_19_5_2_3_1_5527 5 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 117 (accept_3_4 4 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  117 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 59 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 117 (accept_3_4 1 59 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 117))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 117
  (allA_succ_of_accept 57 58 117 (Polychromatic418967fa.accept_24_9_10_21_1_5526 57 58 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 117 (accept_3_5 56 58 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 117 (Polychromatic418967fa.accept_11_10_3_7_1_2564
  54 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 117 (accept_3_5 53
  58 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 117
  (Polychromatic418967fa.accept_7_3_2_5_1_147 52 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 117 (accept_3_5 50 58 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 58 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 117 (Polychromatic418967fa.accept_11_4_3_7_1_828
  48 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 117 (accept_3_5 47
  58 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 117
  (Polychromatic418967fa.accept_7_4_2_5_1_527 46 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 58 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 58 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 117 (accept_3_5 44 58 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 58 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 117 (Polychromatic418967fa.accept_12_6_10_9_1_531
  42 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 117 (accept_3_5 41
  58 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 117
  (Polychromatic418967fa.accept_15_10_13_12_1_3384 40 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 117 (accept_3_5 38 58 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 58 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 117
  (Polychromatic418967fa.accept_17_2_7_15_1_5525 36 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 117 (accept_3_5 35 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 117 (Polychromatic418967fa.accept_25_9_8_17_1_5524 34 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 117 (Polychromatic418967fa.accept_15_3_13_12_1_348 33 58 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 117 (accept_3_5 32 58 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 117
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 117 (accept_3_5 29 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 117 (Polychromatic418967fa.accept_16_12_10_5_1_5457 28 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 117 (accept_3_5 26 58 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 58 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 117
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 117 (accept_3_5 23 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 117 (Polychromatic418967fa.accept_17_5_7_15_1_1230 22 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 117 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 58 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 117 (accept_3_5 20 58 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 117
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 117 (accept_3_5 17 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 117 (Polychromatic418967fa.accept_15_1_13_12_1_347 16 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 117 (accept_3_5 14 58 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 58 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 117
  (Polychromatic418967fa.accept_16_12_10_5_1_5457 12 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 117 (accept_3_5 11 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 117 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 58 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 117 (accept_3_5 8 58 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 117
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 117 (accept_3_5 5 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  117 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 58 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 117 (accept_3_5 2 58 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 58 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 117))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 57 117 (allA_succ_of_accept 56 57 117 (Polychromatic418967fa.accept_18_2_3_9_1_1996 56 57 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 117
  (Polychromatic418967fa.accept_7_6_1_5_1_322 55 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 57 117 3 18 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 57 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 57 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 57 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 57 117 3 17 19 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 57 117
  (Polychromatic418967fa.accept_18_14_3_9_1_4234 50 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 117 (Polychromatic418967fa.accept_16_1_9_5_1_5443 49 57 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 117 3 16 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 117 (Polychromatic418967fa.accept_21_5_15_12_1_5519
  47 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 117
  (Polychromatic418967fa.accept_7_4_1_5_1_540 46 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 57 117 3 15 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 57 117 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 57 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 117 (Polychromatic418967fa.accept_16_11_9_5_1_4412 43 57
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 57 117 3 14 19 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 57 117
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 57 117 (Polychromatic418967fa.accept_21_19_15_12_1_5523 40 57 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 117 3 13 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 38
  57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 117
  (Polychromatic418967fa.accept_18_1_3_9_1_328 37 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 57 117 3 12 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 57 117 (Polychromatic418967fa.accept_21_14_15_12_1_5522 35 57 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 57 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 57 117 3 11 19 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 57 117
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 57 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 117 3 10 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 117 (Polychromatic418967fa.accept_16_13_9_5_1_3302
  29 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 117
  (Polychromatic418967fa.accept_8_4_1_5_1_186 28 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 57 117 3 9 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 57 117 (Polychromatic418967fa.accept_17_9_6_15_1_5454 26 57 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 57 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 57 117 3 8 19 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 57 117
  (Polychromatic418967fa.accept_27_23_3_9_1_5521 23 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 117 (Polychromatic418967fa.accept_21_1_15_12_1_4007 22 57 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 117 3 7 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 57 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 117
  (Polychromatic418967fa.accept_18_1_3_9_1_328 19 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 57 117 3 6 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 57 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 57 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 117 (Polychromatic418967fa.accept_22_16_13_7_1_5520 16 57
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 117 3 5 19 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 117
  (Polychromatic418967fa.accept_16_14_9_5_1_4388 14 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 57 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 117 3 4 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 57 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 117
  (Polychromatic418967fa.accept_7_3_1_5_1_44 10 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 57 117 3 3 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 57 117 (Polychromatic418967fa.accept_17_8_6_15_1_523 8 57 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 117 (Polychromatic418967fa.accept_18_7_3_9_1_1020 7 57 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 117 3 2 19 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 117
  (Polychromatic418967fa.accept_21_5_15_12_1_5519 5 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 57 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 117 3 1 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 117 (Polychromatic418967fa.accept_18_2_3_9_1_1996 2 57 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 117
  (Polychromatic418967fa.accept_16_1_9_5_1_5443 1 57 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 117))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 117 (allA_succ_of_accept 55 56
  117 (accept_3_4 55 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 56 117
  (Polychromatic418967fa.accept_12_6_8_9_1_553 54 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 56 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 117 (accept_3_4 52 56 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 56 117 (Polychromatic418967fa.accept_10_1_6_7_1_710 51 56 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 117 (Polychromatic418967fa.accept_11_6_1_7_1_1315
  50 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 56 117 (accept_3_4 49
  56 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 56 117
  (Polychromatic418967fa.accept_21_6_14_12_1_4003 48 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 56 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 117 (accept_3_4 46 56 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 56 117 (Polychromatic418967fa.accept_16_13_8_5_1_3298 45 56 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 117
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 44 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 56 117 (accept_3_4 43 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 56 117 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 56 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 56 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 117 (accept_3_4 40 56 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 117 (Polychromatic418967fa.accept_11_6_1_7_1_1315
  39 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 117
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 38 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 117 (accept_3_4 37 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 117 (Polychromatic418967fa.accept_16_4_8_5_1_3317 36 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 117 (accept_3_4 34 56 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 117 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 56 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 117
  (Polychromatic418967fa.accept_21_11_14_12_1_5471 32 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 56 117 (accept_3_4 31 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 56 117 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 56 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 56 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 117 (accept_3_4 28 56 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 117 (Polychromatic418967fa.accept_16_11_8_5_1_4366
  27 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 117
  (Polychromatic418967fa.accept_20_6_16_17_1_5518 26 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 117 (accept_3_4 25 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 117 (Polychromatic418967fa.accept_17_7_5_15_1_3184 24 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 117 (accept_3_4 22 56 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 117 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 56 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 117
  (Polychromatic418967fa.accept_16_4_8_5_1_3317 20 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 117 (accept_3_4 19 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 117 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 117 (accept_3_4 16 56 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 117 (Polychromatic418967fa.accept_19_15_18_3_1_1807 15 56 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 117
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 14 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 56 117 (accept_3_4 13 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 56 117 (Polychromatic418967fa.accept_16_12_8_5_1_3316 12 56 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 117 (accept_3_4 10 56 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 117 (Polychromatic418967fa.accept_19_9_18_3_1_5475
  9 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 117
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 117 (accept_3_4 7 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  117 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 56 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 117 (accept_3_4 4 56 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 56 117 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 56 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 117
  (Polychromatic418967fa.accept_19_2_18_3_1_5517 2 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 56 117 (accept_3_4 1 56 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  117)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 117 (allA_succ_of_accept 54 55 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 117 (accept_3_5 53 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 117 (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 55 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 117 (accept_3_5 50 55 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 117 (Polychromatic418967fa.accept_22_5_11_7_1_5516 49 55 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 117
  (Polychromatic418967fa.accept_10_8_5_7_1_358 48 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 117 (accept_3_5 47 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 117 (Polychromatic418967fa.accept_17_11_4_15_1_3150 45 55 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 117 (accept_3_5 44 55 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 55 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 117 (accept_3_5 41 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 55 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 117 (accept_3_5 38 55 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 117 (Polychromatic418967fa.accept_15_7_10_12_1_2403 37 55 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 117
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 117 (accept_3_5 35 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 117 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 55 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 117 (accept_3_5 32 55 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 117 (Polychromatic418967fa.accept_19_12_17_3_1_5515 31 55 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 117 (accept_3_5 29 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 117 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 55 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 117 (accept_3_5 26 55 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 55 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 117
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 117 (accept_3_5 23 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 117 (Polychromatic418967fa.accept_15_6_10_12_1_2538 21 55 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 117 (accept_3_5 20 55 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 117 (Polychromatic418967fa.accept_17_2_4_15_1_5451 19 55
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 117 (accept_3_5 17 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 55 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 117 (accept_3_5 14 55 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 117 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 55 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 117
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 117 (accept_3_5 11 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 117 (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 55 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 117 (accept_3_5 8 55 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 117 (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 55 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 117 (accept_3_5 5 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 117 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 55 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 117 (accept_3_5 2 55 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 55 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 117)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 117 (allA_succ_of_accept 53 54 117 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 54 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 117
  (Polychromatic418967fa.accept_10_2_4_7_1_352 52 54 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 54 117 3 17 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 54 117 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 54 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 117 (Polychromatic418967fa.accept_14_7_12_5_1_1861 49 54
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 117 3 16 18 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 117 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 54 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 117 9 5 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 117 (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 54 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 117 3 14 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 117 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 54 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 117 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 54 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 54 117 3 13 18 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 54 117
  (Polychromatic418967fa.accept_12_2_6_9_1_19 38 54 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 117 (Polychromatic418967fa.accept_19_18_16_3_1_1803 37 54 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 117 9 4 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 117
  (Polychromatic418967fa.accept_12_10_6_9_1_549 34 54 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 54 117 3 11 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 54 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 54 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 117 3 10 18 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 117
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 54 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 117 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 54 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 117 9 3 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 117 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 54 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 117
  (Polychromatic418967fa.accept_11_3_10_7_1_129 25 54 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 117 3 8 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 54 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 54 117 3 7 18 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 54 117
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 54 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 117 9 2 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 117 (Polychromatic418967fa.accept_14_3_12_5_1_153 17 54 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 117
  (Polychromatic418967fa.accept_12_4_6_9_1_548 16 54 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 54 117 3 5 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 54 117 (Polychromatic418967fa.accept_11_3_10_7_1_129 14 54 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 117 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 54 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 117 3 4 18 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 117 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 54 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 117 9 1 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 117 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 54 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 117 3 2 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 117 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 54 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 117 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 54 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 117 3 1 18 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 117
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 54 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 117 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 54 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 117)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  117 (allA_succ_of_accept 52 53 117 (accept_3_4 52 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 53 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 117 (accept_3_4 49 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 53 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 117
  (Polychromatic418967fa.accept_17_13_2_15_1_2151 47 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 117 (accept_3_4 46 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 117 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 117 (accept_3_4 43 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 117 (Polychromatic418967fa.accept_22_20_9_7_1_5514 42 53 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 117
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 117 (accept_3_4 40 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 117 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 117 (accept_3_4 37 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 53 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 117
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 117 (accept_3_4 34 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 117 (Polychromatic418967fa.accept_15_3_8_12_1_900 33 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 117 (accept_3_4 31 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 53 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 117
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 117 (accept_3_4 28 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 117 (accept_3_4 25 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 117 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 53 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 117
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 117 (accept_3_4 22 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 117 (Polychromatic418967fa.accept_17_4_2_15_1_1254 21 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 117 (accept_3_4 19 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 117 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 53 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 117
  (Polychromatic418967fa.accept_19_17_15_3_1_4174 17 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 117 (accept_3_4 16 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 117 (accept_3_4 13 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 117 (Polychromatic418967fa.accept_18_12_17_9_1_5513 12 53 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 117
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 11 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 117 (accept_3_4 10 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 117 (accept_3_4 7 53 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 53 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 117
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 117 (accept_3_4 4 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  117 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 53 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 53 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 117 (accept_3_4 1 53 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 117))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 117
  (allA_succ_of_accept 51 52 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 52 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 117 (accept_3_5 50 52 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 117 (Polychromatic418967fa.accept_11_4_8_7_1_819
  48 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 117 (accept_3_5 47
  52 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 117
  (Polychromatic418967fa.accept_17_12_1_15_1_5472 46 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 52 117 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 52 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 117 (accept_3_5 44 52 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 52 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 117 (Polychromatic418967fa.accept_12_6_4_9_1_544
  42 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 117 (accept_3_5 41
  52 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 117
  (Polychromatic418967fa.accept_14_12_10_5_1_2712 40 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 52 117 13 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 52 117 (accept_3_5 38 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  52 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 52 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 52 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 117 (accept_3_5 35 52 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 117 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 52 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 117
  (Polychromatic418967fa.accept_8_1_4_5_1_48 33 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 117 (accept_3_5 32 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  52 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 52 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 52 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 117 (accept_3_5 29 52 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 117 (Polychromatic418967fa.accept_16_12_4_5_1_2273 28 52 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 117
  (Polychromatic418967fa.accept_19_8_14_3_1_4151 27 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 52 117 13 2 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 52 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 117 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 52 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 117 (accept_3_5 23 52 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 22
  52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 117
  (Polychromatic418967fa.accept_15_6_7_12_1_869 21 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 117 (accept_3_5 20 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  52 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 52 117 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 52 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 117 (accept_3_5 17 52 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 52 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 117
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 117 (accept_3_5 14 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 52
  117 13 1 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12
  52 117 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 52 117 (accept_3_5 11 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 52 117 (Polychromatic418967fa.accept_15_10_7_12_1_2490 10 52 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 52 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 117 (accept_3_5 8 52 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 117
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 117 (accept_3_5 5 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  117 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 52 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 117 (Polychromatic418967fa.accept_15_3_7_12_1_372 3 52 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 117 (accept_3_5 2 52 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 117))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 117 (allA_succ_of_accept 50 51 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 117
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 51 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 51 117 3 16 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 51 117 (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 51 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 51 117 3 15 17 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 51 117
  (Polychromatic418967fa.accept_10_4_1_7_1_371 44 51 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 117 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 51 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 117 3 14 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 41
  51 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 117
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 40 51 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 51 117 3 13 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 51 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 117 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 51 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 117 3 12 17 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 117
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 51 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 117 3 11 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 32
  51 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 117
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 51 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 51 117 3 10 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 51 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 51 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 117 (Polychromatic418967fa.accept_18_10_15_9_1_1054 28 51
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 117 3 9 17 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 51 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 117 3 8 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 117 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 51 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 51 117 3 7 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 51 117 (Polychromatic418967fa.accept_15_5_6_12_1_916 20 51 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 117 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 51 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 117 3 6 17 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 117
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 51 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 117 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 51 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 117 3 5 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 117
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 51 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 51 117 3 4 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 51 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 51 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 117 3 3 17 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 117
  (Polychromatic418967fa.accept_16_8_3_5_1_5512 8 51 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 117 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 51 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 117 3 2 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 51 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 117
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 51 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 51 117 3 1 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 51 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 117 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 51 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  117))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 117 (allA_succ_of_accept 49 50 117 (accept_3_4 49
  50 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 117
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 117 (accept_3_4 46 50 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 50 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 117 (Polychromatic418967fa.accept_23_21_4_2_1_5511
  44 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 117 (accept_3_4 43
  50 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 117
  (Polychromatic418967fa.accept_12_6_2_9_1_537 42 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 50 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 117 (accept_3_4 40 50 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 38
  50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 117 (accept_3_4 37 50
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 117
  (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 50 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 117 (accept_3_4 34 50 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 50 117 (Polychromatic418967fa.accept_20_13_10_17_1_5510 33 50 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 117
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 117 (accept_3_4 31 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 117 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 50 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 117 (accept_3_4 28 50 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 117
  (Polychromatic418967fa.accept_19_7_12_3_1_4169 26 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 117 (accept_3_4 25 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 117 (accept_3_4 22 50 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 117 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 50 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 117
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 117 (accept_3_4 19 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 50 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 117 (accept_3_4 16 50 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 117
  (Polychromatic418967fa.accept_17_14_16_15_1_5509 14 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 50 117 (accept_3_4 13 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 50 117 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 50 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 117 (accept_3_4 10 50 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 117 (Polychromatic418967fa.accept_15_9_5_12_1_1640
  9 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 117
  (Polychromatic418967fa.accept_15_8_5_12_1_4453 8 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 117 (accept_3_4 7 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  117 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 50 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 117 (accept_3_4 4 50 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 117 (Polychromatic418967fa.accept_15_2_5_12_1_369 2
  50 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 117 (accept_3_4 1 50 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 117)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 117 (allA_succ_of_accept 48 49 117 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 49 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 117 (accept_3_5 47 49 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 49 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 117
  (Polychromatic418967fa.accept_16_13_1_5_1_5469 45 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 117 (accept_3_5 44 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 117 (Polychromatic418967fa.accept_21_1_7_12_1_1465 43 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 117 (Polychromatic418967fa.accept_10_2_9_7_1_720 42 49 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 117 (accept_3_5 41 49 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 117
  (Polychromatic418967fa.accept_12_3_1_9_1_202 39 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 117 (accept_3_5 38 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 117 (Polychromatic418967fa.accept_14_9_7_5_1_1105 37 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 117 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 49 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 117 (accept_3_5 35 49 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 49 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 117
  (Polychromatic418967fa.accept_19_14_11_3_1_5508 33 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 117 (accept_3_5 32 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 117 (Polychromatic418967fa.accept_11_9_5_7_1_815 31 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 117 (Polychromatic418967fa.accept_14_2_7_5_1_5450 30 49 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 117 (accept_3_5 29 49 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 117
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 117 (accept_3_5 26 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 117 (Polychromatic418967fa.accept_16_9_1_5_1_2282 25 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 117 (Polychromatic418967fa.accept_15_9_4_12_1_1611 24 49 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 117 (accept_3_5 23 49 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 49 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 117
  (Polychromatic418967fa.accept_18_3_13_9_1_4260 21 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 117 (accept_3_5 20 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 117 (Polychromatic418967fa.accept_21_19_7_12_1_5507 19 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 117 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 49 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 117 (accept_3_5 17 49 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 117
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 117 (accept_3_5 14 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 117 (Polychromatic418967fa.accept_16_13_1_5_1_5469 13 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 117 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 49 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 117 (accept_3_5 11 49 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 49 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 117
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 117 (accept_3_5 8 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  117 (Polychromatic418967fa.accept_15_7_4_12_1_2530 7 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 49 117 (Polychromatic418967fa.accept_16_6_1_5_1_2242 6 49 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 117 (accept_3_5 5 49 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 117
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 117 (accept_3_5 2 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  117 (Polychromatic418967fa.accept_15_1_4_12_1_2401 1 49 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 49 117))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 117 (allA_succ_of_accept
  47 48 117 (Polychromatic418967fa.accept_11_3_4_7_1_114 47 48 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 48 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 48 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 117 3 15 16 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 117
  (Polychromatic418967fa.accept_21_2_6_12_1_5506 44 48 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 48 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 48 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 117 3 14 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 117 (Polychromatic418967fa.accept_11_8_4_7_1_1303
  41 48 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 117
  (Polychromatic418967fa.accept_17_6_14_15_1_5505 40 48 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 48 117 3 13 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 48 117 (Polychromatic418967fa.accept_15_8_3_12_1_1657 38 48 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 117 (Polychromatic418967fa.accept_15_7_3_12_1_365 37 48 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 117 3 12 16 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 117
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 48 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 117 (Polychromatic418967fa.accept_18_16_12_9_1_5504 34 48 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 117 3 11 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 32
  48 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 117
  (Polychromatic418967fa.accept_19_12_10_3_1_5503 31 48 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 117 3 10 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 48 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 117 (Polychromatic418967fa.accept_15_13_3_12_1_1609 28 48
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 117 3 9 16 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 117
  (Polychromatic418967fa.accept_19_7_10_3_1_4149 26 48 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 48 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 48 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 117 3 8 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 117 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 48 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 117
  (Polychromatic418967fa.accept_7_1_6_5_1_39 22 48 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 48 117 3 7 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 48 117 (Polychromatic418967fa.accept_17_3_14_15_1_5502 20 48 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 117 (Polychromatic418967fa.accept_10_9_8_7_1_714 19 48 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 117 3 6 16 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 117
  (Polychromatic418967fa.accept_15_2_3_12_1_891 17 48 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 117 (Polychromatic418967fa.accept_17_16_14_15_1_1250 16 48 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 117 3 5 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 117 (Polychromatic418967fa.accept_11_3_4_7_1_114 14 48 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 117
  (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 48 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 117 3 4 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 48 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 117 (Polychromatic418967fa.accept_18_10_12_9_1_2012 10 48
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 117 3 3 16 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 117
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 48 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 117 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 48 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 117 3 2 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 117 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 48 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 117
  (Polychromatic418967fa.accept_7_4_6_5_1_141 4 48 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 48 117 3 1 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 48 117 (Polychromatic418967fa.accept_15_2_3_12_1_891 2 48 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 48 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  117)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 117 (allA_succ_of_accept 46 47 117 (accept_3_4 46 47
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 117
  (Polychromatic418967fa.accept_17_11_13_15_1_2140 45 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 117 (accept_3_4 43 47 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 117
  (Polychromatic418967fa.accept_22_19_3_7_1_5501 41 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 117 (accept_3_4 40 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 117 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 117 (accept_3_4 37 47 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 117 (Polychromatic418967fa.accept_15_6_2_12_1_885 36 47 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 117
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 35 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 117 (accept_3_4 34 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 117 (Polychromatic418967fa.accept_15_3_2_12_1_2469 33 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 117 (accept_3_4 31 47 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 117
  (Polychromatic418967fa.accept_15_14_2_12_1_2472 29 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 117 (accept_3_4 28 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 117 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 117 (accept_3_4 25 47 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 117 (Polychromatic418967fa.accept_20_4_7_17_1_5500 24 47 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 117
  (Polychromatic418967fa.accept_25_23_22_17_1_5499 23 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 47 117 (accept_3_4 22 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 47 117 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 47 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 117 (accept_3_4 19 47 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  47 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 117
  (Polychromatic418967fa.accept_16_1_15_5_1_708 17 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 117 (accept_3_4 16 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 117 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 117 (accept_3_4 13 47 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 117 (Polychromatic418967fa.accept_18_12_11_9_1_4257 12 47 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 117
  (Polychromatic418967fa.accept_17_11_13_15_1_2140 11 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 47 117 (accept_3_4 10 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 47 117 (Polychromatic418967fa.accept_20_9_7_17_1_1655 9 47 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 117 (accept_3_4 7 47 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 117
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 5 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 117 (accept_3_4 4 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  117 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 47 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 47 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 117 (accept_3_4 1 47 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 47 117))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 117
  (allA_succ_of_accept 45 46 117 (Polychromatic418967fa.accept_21_3_4_12_1_1462 45 46 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 46 117 (accept_3_5 44 46 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 46 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 117 (Polychromatic418967fa.accept_11_9_2_7_1_1298
  42 46 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 117 (accept_3_5 41
  46 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 117
  (Polychromatic418967fa.accept_21_19_4_12_1_4027 40 46 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 46 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 117 (accept_3_5 38 46 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 46 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 46 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 36
  46 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 117 (accept_3_5 35 46
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 117
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 46 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 46 117 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 46 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 117 (accept_3_5 32 46 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 46 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 30
  46 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 117 (accept_3_5 29 46
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 117
  (Polychromatic418967fa.accept_15_13_1_12_1_1638 28 46 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 46 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 117 (accept_3_5 26 46 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 46 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 46 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 117 (Polychromatic418967fa.accept_19_5_8_3_1_5498
  24 46 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 117 (accept_3_5 23
  46 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 117
  (Polychromatic418967fa.accept_7_1_4_5_1_35 22 46 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 46 117 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 46 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 117 (accept_3_5 20 46 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 46 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 117 (Polychromatic418967fa.accept_12_6_10_9_1_531
  18 46 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 117 (accept_3_5 17
  46 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 117
  (Polychromatic418967fa.accept_7_2_4_5_1_313 16 46 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 46 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 117 (accept_3_5 14 46 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 46 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 46 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 117
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 46 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 46 117 (accept_3_5 11 46 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  46 117 (Polychromatic418967fa.accept_16_10_14_5_1_5496 10 46 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 46 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 46 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 117 (accept_3_5 8 46 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 46 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 117
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 46 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 46 117 (accept_3_5 5 46 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46
  117 (Polychromatic418967fa.accept_15_4_1_12_1_914 4 46 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 46 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 117 (accept_3_5 2 46 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 46 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 117))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 45 117 (allA_succ_of_accept 44 45 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 45 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 117
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 45 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 45 117 3 14 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 45 117 (Polychromatic418967fa.accept_16_9_13_5_1_2238 41 45 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 117 (Polychromatic418967fa.accept_14_12_3_5_1_1868 40 45
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 45 117 3 13 15 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 117
  (Polychromatic418967fa.accept_10_8_5_7_1_358 38 45 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 45 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 117 9 4 5 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 117 (Polychromatic418967fa.accept_20_15_5_17_1_5495 35 45
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 117
  (Polychromatic418967fa.accept_16_2_13_5_1_2257 34 45 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 45 117 3 11 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 45 117 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 45 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 117 (Polychromatic418967fa.accept_19_12_7_3_1_5494 31 45
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 117 3 10 15 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 117
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 45 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 45 117 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 45 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 117 9 3 5 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 117 (Polychromatic418967fa.accept_14_12_3_5_1_1868 26 45 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 117
  (Polychromatic418967fa.accept_16_9_13_5_1_2238 25 45 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 45 117 3 8 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 45 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 45 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 45 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 117 3 7 15 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 45 117
  (Polychromatic418967fa.accept_21_20_3_12_1_5493 20 45 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 117 (Polychromatic418967fa.accept_23_19_22_2_1_5492 19 45 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 117 9 2 5 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 117 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 45 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 117
  (Polychromatic418967fa.accept_7_2_3_5_1_34 16 45 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 45 117 3 5 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 45 117 (Polychromatic418967fa.accept_19_14_7_3_1_5491 14 45 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 117 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 45 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 117 3 4 15 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 117
  (Polychromatic418967fa.accept_20_11_5_17_1_5490 11 45 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 45 117 (Polychromatic418967fa.accept_16_10_13_5_1_3292 10 45 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 117 9 1 5 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 45 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 117
  (Polychromatic418967fa.accept_21_7_3_12_1_1455 7 45 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 45 117 3 2 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 45 117 (Polychromatic418967fa.accept_17_5_11_15_1_5445 5 45 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 117 (Polychromatic418967fa.accept_17_4_11_15_1_3170 4 45 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 117 3 1 15 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 117
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 45 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 45 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 45 117))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 117
  (allA_succ_of_accept 43 44 117 (accept_3_4 43 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  44 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 117 (accept_3_4 40 44 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 44 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 117
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 117 (accept_3_4 37 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 117 (Polychromatic418967fa.accept_16_4_12_5_1_2287 36 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 117 (accept_3_4 34 44 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 44 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 117
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 117 (accept_3_4 31 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 117 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 117 (accept_3_4 28 44 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 117 (Polychromatic418967fa.accept_19_8_6_3_1_4164 27 44 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 117
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 44 117 (accept_3_4 25 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 44 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 44 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 117 (accept_3_4 22 44 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 117 (Polychromatic418967fa.accept_10_1_4_7_1_374
  21 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 117
  (Polychromatic418967fa.accept_16_4_12_5_1_2287 20 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 117 (accept_3_4 19 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 117 (accept_3_4 16 44 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 117 (Polychromatic418967fa.accept_26_15_18_13_1_5489 15 44 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 117
  (Polychromatic418967fa.accept_21_14_2_12_1_5488 14 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 117 (accept_3_4 13 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 117 (accept_3_4 10 44 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 44 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 117
  (Polychromatic418967fa.accept_16_8_12_5_1_200 8 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 117 (accept_3_4 7 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  117 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 44 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 117 (accept_3_4 4 44 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 44 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 2
  44 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 117 (accept_3_4 1 44 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 117)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  117 (allA_succ_of_accept 42 43 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 117 (accept_3_5 41 43 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 43 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 39
  43 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 117 (accept_3_5 38 43
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 117
  (Polychromatic418967fa.accept_34_3_9_15_1_5487 37 43 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 43 117 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 43 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 117 (accept_3_5 35 43 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 43 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 117 (Polychromatic418967fa.accept_15_3_13_12_1_348
  33 43 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 117 (accept_3_5 32
  43 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 117
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 43 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 43 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 117 (accept_3_5 29 43 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 43 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 27
  43 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 117 (accept_3_5 26 43
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 117
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 43 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 43 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 43 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 117 (accept_3_5 23 43 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 43 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 117 (Polychromatic418967fa.accept_18_3_7_9_1_5486
  21 43 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 117 (accept_3_5 20
  43 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 117
  (Polychromatic418967fa.accept_21_19_1_12_1_5485 19 43 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 43 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 117 (accept_3_5 17 43 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 43 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 117 (Polychromatic418967fa.accept_10_5_3_7_1_1108
  15 43 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 117 (accept_3_5 14
  43 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 117
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 43 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 43 117 (Polychromatic418967fa.accept_24_12_19_21_1_5484 12 43 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 117 (accept_3_5 11 43 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 43 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 117 (Polychromatic418967fa.accept_16_9_11_5_1_2279
  9 43 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 117 (accept_3_5 8 43
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 117
  (Polychromatic418967fa.accept_16_7_11_5_1_4402 7 43 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 117 (accept_3_5 5 43 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 43
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 117 (accept_3_5 2 43 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 117 (Polychromatic418967fa.accept_15_1_13_12_1_347
  1 43 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  117))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 117 (allA_succ_of_accept 41 42 117
  (Polychromatic418967fa.accept_27_14_15_9_1_5483 41 42 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 117 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 42 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 117 3 13 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 117 (Polychromatic418967fa.accept_11_5_9_7_1_411 38
  42 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 117
  (Polychromatic418967fa.accept_18_1_6_9_1_2001 37 42 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 117 3 12 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 117 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 42 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 42 117 3 11 14 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 42 117
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 42 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 117 3 10 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 117 (Polychromatic418967fa.accept_10_9_2_7_1_1096
  29 42 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 117
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 42 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 42 117 3 9 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 42 117 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 42 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 117 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 42 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 117 3 8 14 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 117 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 42 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 117 3 7 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 117 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 42 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 117 3 6 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 117 (Polychromatic418967fa.accept_23_17_19_2_1_5482 17 42 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 117 (Polychromatic418967fa.accept_11_5_9_7_1_411 16 42 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 42 117 3 5 14 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 42 117
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 42 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 42 117 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 42 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 117 3 4 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 117
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 42 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 42 117 3 3 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 42 117 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 42 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 117 3 2 14 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 117
  (Polychromatic418967fa.accept_10_5_2_7_1_345 5 42 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 117 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 42 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 117 3 1 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 117 (Polychromatic418967fa.accept_11_2_9_7_1_124 2 42 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 117
  (Polychromatic418967fa.accept_18_1_6_9_1_2001 1 42 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 117)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 117 (allA_succ_of_accept 40 41 117
  (accept_3_4 40 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 117
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 41 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 117 (accept_3_4 37 41 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 41 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 117
  (Polychromatic418967fa.accept_22_13_19_7_1_2558 35 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 117 (accept_3_4 34 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 117 (Polychromatic418967fa.accept_16_1_9_5_1_5443 33 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 117 (accept_3_4 31 41 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 117 (Polychromatic418967fa.accept_16_14_9_5_1_4388 30 41 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 117
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 117 (accept_3_4 28 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 117 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 41 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 117 (accept_3_4 25 41 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 117 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 41 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 117
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 23 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 117 (accept_3_4 22 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 117 (Polychromatic418967fa.accept_22_21_19_7_1_5481 21 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 117 (accept_3_4 19 41 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 41 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 117
  (Polychromatic418967fa.accept_16_1_9_5_1_5443 17 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 117 (accept_3_4 16 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 41 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 117 (accept_3_4 13 41 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 117 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 41 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 117
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 117 (accept_3_4 10 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 117 (Polychromatic418967fa.accept_17_9_7_15_1_4346 9 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 117 (accept_3_4 7 41 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 117 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 41 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 117
  (Polychromatic418967fa.accept_17_5_7_15_1_1230 5 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 117 (accept_3_4 4 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  117 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 41 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 41 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 117 (accept_3_4 1 41 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 117))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 117 (allA_succ_of_accept 39 40 117
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 117 (accept_3_5 38 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 117 (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 40 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 117 (accept_3_5 35 40 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 117 (Polychromatic418967fa.accept_22_12_18_7_1_5480 34 40
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 117
  (Polychromatic418967fa.accept_18_15_4_9_1_4204 33 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 117 (accept_3_5 32 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 117 (Polychromatic418967fa.accept_12_6_4_9_1_544 30 40 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 117 (accept_3_5 29 40 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 117 (Polychromatic418967fa.accept_15_13_10_12_1_2503 28 40 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 117
  (Polychromatic418967fa.accept_16_11_8_5_1_4366 27 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 117 (accept_3_5 26 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 117 (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 40 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 117 (accept_3_5 23 40 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 117 (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 40
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 117
  (Polychromatic418967fa.accept_14_7_12_5_1_1861 21 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 117 (accept_3_5 20 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 117 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 40 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 117 (accept_3_5 17 40 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 117 (Polychromatic418967fa.accept_19_16_2_3_1_5479 16 40 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 117
  (Polychromatic418967fa.accept_18_15_4_9_1_4204 15 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 117 (accept_3_5 14 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 117 (Polychromatic418967fa.accept_16_12_8_5_1_3316 12 40 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 117 (accept_3_5 11 40 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 117 (Polychromatic418967fa.accept_14_10_12_5_1_3466 10 40
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 117
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 117 (accept_3_5 8 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  117 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 117 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 40 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 117 (accept_3_5 5 40 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 117 (Polychromatic418967fa.accept_16_4_8_5_1_3317 4 40 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 117 (Polychromatic418967fa.accept_14_3_12_5_1_153 3
  40 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 117 (accept_3_5 2 40 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  117)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 117 (allA_succ_of_accept 38 39 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 39 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 117 3 12 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 117 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  35 39 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 117 3 11 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 117 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 39 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 117 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 39 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 117 3 10 13 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 117
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 39 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 117 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 39 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 117 3 9 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 39 117 13 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 39 117 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 39 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 39 117 3 8 13 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 39 117
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 39 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 117 3 7 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 39 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 117
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 39 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 39 117 3 6 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 39 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 39 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 39 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 39 117 3 5 13 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 39 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 39 117 13 1 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 39 117 3 4 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 39 117 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 39 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 117 3 3 13 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 117
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 39 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 117 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 39 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 39 117 3 2 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 39 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 39 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 117
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 39 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 39 117 3 1 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 39 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 39 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 117)))))))))))))))))))))))))))))))))))))))
  (allB_succ 38 117 (allA_succ_of_accept 37 38 117 (accept_3_4 37 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 38 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 38 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 38 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 117 (accept_3_4 34 38 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 117 (Polychromatic418967fa.accept_15_3_8_12_1_900
  33 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 117
  (Polychromatic418967fa.accept_22_10_16_7_1_2608 32 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 117 (accept_3_4 31 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 38 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 117 (accept_3_4 28 38 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 117
  (Polychromatic418967fa.accept_14_12_10_5_1_2712 26 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 117 (accept_3_4 25 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 117 (Polychromatic418967fa.accept_18_6_2_9_1_3056 24 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 117 (accept_3_4 22 38 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 117 (Polychromatic418967fa.accept_18_3_2_9_1_1013 21 38 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 117
  (Polychromatic418967fa.accept_11_9_5_7_1_815 20 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 117 (accept_3_4 19 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 117 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 38 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 117 (accept_3_4 16 38 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 117
  (Polychromatic418967fa.accept_22_14_16_7_1_5478 14 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 117 (accept_3_4 13 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 117 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 117 (accept_3_4 10 38 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 38 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 117
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 117 (accept_3_4 7 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  117 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 38 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 38 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 117 (accept_3_4 4 38 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 38
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 117 (accept_3_4 1 38 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 117)))))))))))))))))))))))))))))))))))))) (allB_succ 37 117
  (allA_succ_of_accept 36 37 117 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 37 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 117 (accept_3_5 35 37 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 37 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 117 (Polychromatic418967fa.accept_15_3_7_12_1_372
  33 37 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 117 (accept_3_5 32
  37 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 117
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 37 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 117 (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 37 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 117 (accept_3_5 29 37 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 117 (Polychromatic418967fa.accept_12_3_1_9_1_202
  27 37 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 117 (accept_3_5 26
  37 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 117
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 37 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 37 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 117 (accept_3_5 23 37 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 37 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 117 (Polychromatic418967fa.accept_14_7_9_5_1_529
  21 37 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 117 (accept_3_5 20
  37 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 117
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 37 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 37 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 117 (accept_3_5 17 37 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 117 (Polychromatic418967fa.accept_12_3_1_9_1_202
  15 37 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 117 (accept_3_5 14
  37 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 117
  (Polychromatic418967fa.accept_22_13_15_7_1_5477 13 37 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 37 117 (Polychromatic418967fa.accept_17_12_3_15_1_5476 12 37 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 117 (accept_3_5 11 37 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 37 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 37 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 117 (Polychromatic418967fa.accept_19_9_18_3_1_5475
  9 37 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 117 (accept_3_5 8 37
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 117
  (Polychromatic418967fa.accept_14_7_9_5_1_529 7 37 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 117 (Polychromatic418967fa.accept_15_6_7_12_1_869 6 37 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 117 (accept_3_5 5 37 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  37 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 117 (accept_3_5 2 37 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 117 (Polychromatic418967fa.accept_17_1_3_15_1_2153
  1 37 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37
  117))))))))))))))))))))))))))))))))))))) (allB_succ 36 117 (allA_succ_of_accept 35 36 117
  (Polychromatic418967fa.accept_15_5_6_12_1_916 35 36 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 36 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 117 3 11 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 32
  36 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 117
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 36 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 117 3 10 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 117 (Polychromatic418967fa.accept_21_8_15_12_1_5474 29 36 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 117 (Polychromatic418967fa.accept_16_12_4_5_1_2273 28 36
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 36 117 9 3 4 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 36 117
  (Polychromatic418967fa.accept_11_4_3_7_1_828 26 36 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 36 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 117 3 8 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 117 (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 36 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 117
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 22 36 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 36 117 3 7 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 36 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 36 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 117 (Polychromatic418967fa.accept_20_19_16_17_1_5473 19 36
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 117 9 2 4 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 117
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 36 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 117 (Polychromatic418967fa.accept_19_16_17_3_1_2916 16 36 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 117 3 5 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 117 (Polychromatic418967fa.accept_19_14_17_3_1_4137 14 36
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 117
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 36 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 117 3 4 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 36 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 36 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 36 117 9 1 4 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 36 117
  (Polychromatic418967fa.accept_16_8_4_5_1_4379 8 36 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 117 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 36 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 117 3 2 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 117 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 36 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 117
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 36 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 36 117 3 1 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 36 117 (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 36 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 36 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 117))))))))))))))))))))))))))))))))))))
  (allB_succ 35 117 (allA_succ_of_accept 34 35 117 (accept_3_4 34 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 35 117 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 35 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 117 (accept_3_4 31 35 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  35 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 117
  (Polychromatic418967fa.accept_17_12_1_15_1_5472 29 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 117 (accept_3_4 28 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 117 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 117 (accept_3_4 25 35 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 117 (Polychromatic418967fa.accept_15_9_5_12_1_1640 24 35 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 117
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 117 (accept_3_4 22 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 117 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 117 (accept_3_4 19 35 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 117
  (Polychromatic418967fa.accept_15_2_5_12_1_369 17 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 117 (accept_3_4 16 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 117 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 117 (accept_3_4 13 35 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 117 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 35 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 117
  (Polychromatic418967fa.accept_21_11_14_12_1_5471 11 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 35 117 (accept_3_4 10 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 35 117 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 35 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 117 (accept_3_4 7 35 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 117
  (Polychromatic418967fa.accept_19_5_16_3_1_1820 5 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 117 (accept_3_4 4 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  117 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 35 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 117 (accept_3_4 1 35 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 117))))))))))))))))))))))))))))))))))) (allB_succ 34 117 (allA_succ_of_accept 33 34 117
  (Polychromatic418967fa.accept_10_3_4_7_1_353 33 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 117 (accept_3_5 32 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 117 (Polychromatic418967fa.accept_12_6_10_9_1_531 30 34 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 117 (accept_3_5 29 34 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 117 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 34 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 117 (accept_3_5 26 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 117 (Polychromatic418967fa.accept_15_9_4_12_1_1611 24 34 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 117 (accept_3_5 23 34 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 34 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 117
  (Polychromatic418967fa.accept_10_1_4_7_1_374 21 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 117 (accept_3_5 20 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 34 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 117 (accept_3_5 17 34 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 117 (Polychromatic418967fa.accept_15_1_4_12_1_2401 16 34 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 117 (accept_3_5 14 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 34 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 117 (accept_3_5 11 34 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 117 (Polychromatic418967fa.accept_19_10_15_3_1_5470 10 34 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 117
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 117 (accept_3_5 8 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 117 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 34 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 117 (accept_3_5 5 34 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 34 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 117 (accept_3_5 2 34 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 34
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 117))))))))))))))))))))))))))))))))))
  (allB_succ 33 117 (allA_succ_of_accept 32 33 117 (Polychromatic418967fa.accept_15_2_3_12_1_891 32 33 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 117
  (Polychromatic418967fa.accept_16_15_1_5_1_2265 31 33 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 117 3 10 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 117 (Polychromatic418967fa.accept_16_13_1_5_1_5469 29 33 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 117 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 33 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 117 3 9 11 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 117
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 26 33 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 117 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 33 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 117 3 8 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 117 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 33 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 117
  (Polychromatic418967fa.accept_15_7_3_12_1_365 22 33 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 117 3 7 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 117 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 33 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 117 (Polychromatic418967fa.accept_26_19_7_13_1_5468 19 33
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 117 3 6 11 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 117
  (Polychromatic418967fa.accept_15_2_3_12_1_891 17 33 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 117 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 33 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 117 3 5 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 117 (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 33 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 117
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 33 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 117 3 4 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 117 (Polychromatic418967fa.accept_17_11_16_15_1_5467 11 33 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 117 (Polychromatic418967fa.accept_18_10_15_9_1_1054 10 33
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 117 3 3 11 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 117
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 33 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 117 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 33 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 117 3 2 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 117 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 33 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 117
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 33 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 117 3 1 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 117 (Polychromatic418967fa.accept_15_2_3_12_1_891 2 33 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 117 (Polychromatic418967fa.accept_17_1_16_15_1_4315 1 33 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 117)))))))))))))))))))))))))))))))))
  (allB_succ 32 117 (allA_succ_of_accept 31 32 117 (accept_3_4 31 32 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 32 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 117 (accept_3_4 28 32 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 27
  32 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 117
  (Polychromatic418967fa.accept_19_7_13_3_1_4171 26 32 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 117 (accept_3_4 25 32 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 117 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 32 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 117 (accept_3_4 22 32 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 117 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 32 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 117
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 32 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 117 (accept_3_4 19 32 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 117 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 32 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 117 (accept_3_4 16 32 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 32 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 117
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 32 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 117 (accept_3_4 13 32 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 117 (Polychromatic418967fa.accept_19_12_13_3_1_5447 12 32 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 117 (accept_3_4 10 32 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 32 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 117
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 32 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 117 (accept_3_4 7 32 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  117 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 32 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 117 (accept_3_4 4 32 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 117 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 32 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  32 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 117 (accept_3_4 1 32 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 117)))))))))))))))))))))))))))))))) (allB_succ 31 117
  (allA_succ_of_accept 30 31 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 117 (accept_3_5 29 31 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 117 (Polychromatic418967fa.accept_11_5_9_7_1_411
  27 31 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 117 (accept_3_5 26
  31 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 117
  (Polychromatic418967fa.accept_20_5_11_17_1_5466 25 31 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 117 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 31 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 117 (accept_3_5 23 31 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 117 (Polychromatic418967fa.accept_18_3_13_9_1_4260
  21 31 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 117 (accept_3_5 20
  31 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 117
  (Polychromatic418967fa.accept_15_4_1_12_1_914 19 31 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 117 (accept_3_5 17 31 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  31 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 117 (accept_3_5 14 31
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 117
  (Polychromatic418967fa.accept_11_2_9_7_1_124 13 31 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 31 117 (Polychromatic418967fa.accept_14_12_3_5_1_1868 12 31 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 117 (accept_3_5 11 31 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 31 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 31
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 117 (accept_3_5 8 31 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 117 (Polychromatic418967fa.accept_19_7_12_3_1_4169
  7 31 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 117 (accept_3_5 5 31 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 117 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 31 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 117 (accept_3_5 2 31 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 31 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 117))))))))))))))))))))))))))))))) (allB_succ 30 117
  (allA_succ_of_accept 29 30 117 (Polychromatic418967fa.accept_18_11_12_9_1_992 29 30 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 117 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 30 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 117 3 9 10 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 117
  (Polychromatic418967fa.accept_11_4_8_7_1_819 26 30 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 30 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 117 3 8 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 117
  (Polychromatic418967fa.accept_12_10_6_9_1_549 22 30 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 117 3 7 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 30 117 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 30 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 117 3 6 10 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 117
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 30 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 117 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 30 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 117 3 5 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 117 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 30 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 117
  (Polychromatic418967fa.accept_19_13_11_3_1_5465 13 30 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 117 3 4 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 30 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 117 3 3 10 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 117
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 30 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 117 3 2 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 117 (Polychromatic418967fa.accept_17_5_13_15_1_5464 5 30 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 117
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 30 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 117 3 1 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 117 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 30 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 117 (Polychromatic418967fa.accept_19_1_11_3_1_5463 1 30 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 117)))))))))))))))))))))))))))))) (allB_succ
  29 117 (allA_succ_of_accept 28 29 117 (accept_3_4 28 29 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 29 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 29 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 117 (accept_3_4 25 29 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 24
  29 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 117
  (Polychromatic418967fa.accept_24_23_5_21_1_5462 23 29 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 117 (accept_3_4 22 29 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 117 (Polychromatic418967fa.accept_25_21_4_17_1_5461 21 29 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 117 (accept_3_4 19 29 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 29 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 117
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 29 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 117 (accept_3_4 16 29 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 117 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 29 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 29 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 117 (accept_3_4 13 29 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 117 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 29 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 117
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 29 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 117 (accept_3_4 10 29 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 117 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 29 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 117 (accept_3_4 7 29 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 29 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 117
  (Polychromatic418967fa.accept_19_5_10_3_1_5460 5 29 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 117 (accept_3_4 4 29 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  117 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 29 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 29 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 117 (accept_3_4 1 29 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 117))))))))))))))))))))))))))))) (allB_succ 28 117 (allA_succ_of_accept 27 28 117
  (Polychromatic418967fa.accept_20_7_8_17_1_1635 27 28 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 117 (accept_3_5 26 28 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 117 (Polychromatic418967fa.accept_16_8_12_5_1_200 24 28 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 117 (accept_3_5 23 28 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 117 (Polychromatic418967fa.accept_17_5_11_15_1_5445 22 28 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 117
  (Polychromatic418967fa.accept_17_4_11_15_1_3170 21 28 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 117 (accept_3_5 20 28 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 117 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 28 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 117 (accept_3_5 17 28 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 117 (Polychromatic418967fa.accept_15_1_13_12_1_347 16 28 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 117
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 28 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 117 (accept_3_5 14 28 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 117 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 28 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 117 (accept_3_5 11 28 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 117 (Polychromatic418967fa.accept_15_10_13_12_1_3384 10 28 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 117
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 28 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 117 (accept_3_5 8 28 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  117 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 117 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 28 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 117 (accept_3_5 5 28 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 117 (Polychromatic418967fa.accept_16_4_12_5_1_2287 4 28 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 117 (Polychromatic418967fa.accept_15_3_13_12_1_348
  3 28 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 117 (accept_3_5 2 28
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 117 (Polychromatic418967fa.accept_6_1_4_3_1_14
  1 28 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 117))))))))))))))))))))))))))))
  (allB_succ 27 117 (allA_succ_of_accept 26 27 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 117
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 27 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 27 117 3 8 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 27 117 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 27 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 117 3 7 9 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 117
  (Polychromatic418967fa.accept_11_9_5_7_1_815 20 27 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 117 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 27 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 117 9 2 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 27 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 117
  (Polychromatic418967fa.accept_20_16_7_17_1_5459 16 27 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 27 117 3 5 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 27 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 117 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 27 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 117 3 4 9 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 117
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 27 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 117 9 1 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 27 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 117
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 27 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 27 117 3 2 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 27 117 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 27 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 27 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 117 3 1 9 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 27 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 117))))))))))))))))))))))))))) (allB_succ 26 117 (allA_succ_of_accept 25
  26 117 (accept_3_4 25 26 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 117
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 26 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 117 (accept_3_4 22 26 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 117 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 26 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 117 (Polychromatic418967fa.accept_23_20_3_2_1_5458
  20 26 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 117 (accept_3_4 19
  26 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 117
  (Polychromatic418967fa.accept_12_6_2_9_1_537 18 26 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 26 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 117 (accept_3_4 16 26 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 117 (Polychromatic418967fa.accept_11_3_4_7_1_114
  14 26 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 26 117 13 1 2 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 26 117
  (Polychromatic418967fa.accept_16_12_10_5_1_5457 12 26 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 26 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 117 (accept_3_4 10 26 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 26 117 (Polychromatic418967fa.accept_20_9_6_17_1_1654 9 26 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 117 (Polychromatic418967fa.accept_11_8_4_7_1_1303 8
  26 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 117 (accept_3_4 7 26 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 117 (Polychromatic418967fa.accept_12_6_2_9_1_537 6
  26 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 117
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 26 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 117 (accept_3_4 4 26 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26
  117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 117 (Polychromatic418967fa.accept_25_2_1_17_1_5456 2 26 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 117 (accept_3_4 1 26 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 117)))))))))))))))))))))))))) (allB_succ 25 117 (allA_succ_of_accept 24 25 117
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 25 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 117 (accept_3_5 23 25 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 25 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 117 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 25 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 117 (accept_3_5 20 25 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 117 (Polychromatic418967fa.accept_21_19_4_12_1_4027 19 25
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 117
  (Polychromatic418967fa.accept_10_8_5_7_1_358 18 25 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 117 (accept_3_5 17 25 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 25 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 117 (accept_3_5 14 25 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 25 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 117
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 25 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 117 (accept_3_5 11 25 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 25 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 25 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 117 (accept_3_5 8 25 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 117 (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 25 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 117
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 25 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 117 (accept_3_5 5 25 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 117 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 25 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 117 (accept_3_5 2 25 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 25 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 117))))))))))))))))))))))))) (allB_succ 24 117
  (allA_succ_of_accept 23 24 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 24 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 24 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 117 3 7 8 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 117
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 24 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 117 (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 24 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 117 3 6 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 117 (Polychromatic418967fa.accept_19_17_5_3_1_5455 17 24 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 117
  (Polychromatic418967fa.accept_7_2_3_5_1_34 16 24 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 117 3 5 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 117 (Polychromatic418967fa.accept_15_14_9_12_1_2498 14 24 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 117 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 24 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 117 3 4 8 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 117
  (Polychromatic418967fa.accept_10_1_4_7_1_374 11 24 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 117 (Polychromatic418967fa.accept_15_10_9_12_1_2497 10 24 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 117 3 3 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 24 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 117
  (Polychromatic418967fa.accept_18_7_6_9_1_4205 7 24 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 117 3 2 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 117 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 24 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 117 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 24 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 117 3 1 8 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 117
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 24 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 24 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 117)))))))))))))))))))))))) (allB_succ 23 117 (allA_succ_of_accept 22 23
  117 (accept_3_4 22 23 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 117
  (Polychromatic418967fa.accept_14_7_9_5_1_529 21 23 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 117 (accept_3_4 19 23 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 17
  23 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 117 (accept_3_4 16 23
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 117
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 23 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 117 (accept_3_4 13 23 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 117 (Polychromatic418967fa.accept_16_12_7_5_1_1412 12 23 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 117
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 23 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 117 (accept_3_4 10 23 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 117 (Polychromatic418967fa.accept_17_9_6_15_1_5454 9 23 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 117 (accept_3_4 7 23 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 117
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 23 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 117 (accept_3_4 4 23 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  117 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 23 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 117 (accept_3_4 1 23 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 117))))))))))))))))))))))) (allB_succ 22 117 (allA_succ_of_accept 21 22 117
  (Polychromatic418967fa.accept_15_6_7_12_1_869 21 22 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 117 (accept_3_5 20 22 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 22 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 117 (accept_3_5 17 22 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 117 (Polychromatic418967fa.accept_24_16_22_21_1_5453 16 22 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 117 (accept_3_5 14 22 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 22 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 117 (Polychromatic418967fa.accept_18_12_4_9_1_5452 12 22 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 117 (accept_3_5 11 22 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 117 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 22 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 117
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 22 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 117 (accept_3_5 8 22 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 22 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 117 (accept_3_5 5 22 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 22 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 117 (accept_3_5 2 22 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 22
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 117)))))))))))))))))))))) (allB_succ 21
  117 (allA_succ_of_accept 20 21 117 (Polychromatic418967fa.accept_15_5_6_12_1_916 20 21 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 117 (Polychromatic418967fa.accept_17_2_4_15_1_5451
  19 21 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 117 3 6 7 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 117
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 21 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 117 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 21 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 117 3 5 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 117 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 21 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 117
  (Polychromatic418967fa.accept_18_13_3_9_1_4233 13 21 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 117 3 4 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 117 (Polychromatic418967fa.accept_17_11_4_15_1_3150 11 21 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 117 (Polychromatic418967fa.accept_15_10_6_12_1_1645 10 21
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 117 3 3 7 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 117
  (Polychromatic418967fa.accept_18_8_3_9_1_4232 8 21 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 117 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 21 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 117 3 2 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 117 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 21 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 117
  (Polychromatic418967fa.accept_10_4_1_7_1_371 4 21 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 117 3 1 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 117 (Polychromatic418967fa.accept_14_2_7_5_1_5450 2 21 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 117 (Polychromatic418967fa.accept_18_1_3_9_1_328 1 21 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 117))))))))))))))))))))) (allB_succ 20 117
  (allA_succ_of_accept 19 20 117 (accept_3_4 19 20 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  20 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 20 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 20 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 117 (accept_3_4 16 20 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 20 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 20 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 117
  (Polychromatic418967fa.accept_17_14_3_15_1_5449 14 20 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 20 117 (accept_3_4 13 20 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  20 117 (Polychromatic418967fa.accept_16_12_4_5_1_2273 12 20 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 20 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 117 (accept_3_4 10 20 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 20 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 20 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 117
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 20 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 20 117 (accept_3_4 7 20 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20
  117 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 20 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 20 117 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 117 (accept_3_4 4 20 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 20 117 (Polychromatic418967fa.accept_18_3_2_9_1_1013 3 20 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 117 (Polychromatic418967fa.accept_11_2_9_7_1_124 2
  20 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 117 (accept_3_4 1 20 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 117)))))))))))))))))))) (allB_succ 19 117 (allA_succ_of_accept
  18 19 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 19 117 (accept_3_5 17 19 117 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 19 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 117 (Polychromatic418967fa.accept_11_4_8_7_1_819 15 19 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 117 (accept_3_5 14 19 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 117
  (Polychromatic418967fa.accept_17_13_2_15_1_2151 13 19 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 19 117 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 19 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 117 (accept_3_5 11 19 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 19 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 117 (Polychromatic418967fa.accept_15_9_4_12_1_1611
  9 19 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 117 (accept_3_5 8 19
  117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 117
  (Polychromatic418967fa.accept_15_7_4_12_1_2530 7 19 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 19 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 117 (accept_3_5 5 19 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 19 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 117 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3
  19 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 117 (accept_3_5 2 19 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 117 (Polychromatic418967fa.accept_15_1_4_12_1_2401
  1 19 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 117))))))))))))))))))) (allB_succ
  18 117 (allA_succ_of_accept 17 18 117 (Polychromatic418967fa.accept_15_2_3_12_1_891 17 18 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 16
  18 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 117 3 5 6 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 117
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 18 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 117 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 18 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 117 3 4 6 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 117
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 18 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 18 117 9 1 2 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 18 117 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 18 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 117 3 2 6 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 117
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 18 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 18 117 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 18 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 18 117 3 1 6 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 18 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 18 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 117
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 18 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 117)))))))))))))))))) (allB_succ 17 117 (allA_succ_of_accept 16 17 117 (accept_3_4 16 17 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 117 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 17 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 117
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 17 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 117 (accept_3_4 13 17 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 117 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 17 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 117 (Polychromatic418967fa.accept_22_11_17_7_1_5448 11 17 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 117 (accept_3_4 10 17 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 117 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 17 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 117
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 117 (accept_3_4 7 17 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  117 (Polychromatic418967fa.accept_15_6_2_12_1_885 6 17 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 117 (Polychromatic418967fa.accept_15_5_2_12_1_2543 5 17 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 117 (accept_3_4 4 17 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 117 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 17 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 117
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 17 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 117 (accept_3_4 1 17 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  117))))))))))))))))) (allB_succ 16 117 (allA_succ_of_accept 15 16 117 (Polychromatic418967fa.accept_18_15_16_9_1_4299
  15 16 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 117 (accept_3_5 14
  16 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 117
  (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 16 117 (Polychromatic418967fa.accept_18_12_16_9_1_4198 12 16 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 117 (accept_3_5 11 16 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 16 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 16 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 117 (Polychromatic418967fa.accept_11_9_5_7_1_815 9
  16 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 117 (accept_3_5 8 16 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 117
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 16 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 117 (accept_3_5 5 16 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  117 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 16 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 16 117 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 16 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 117 (accept_3_5 2 16 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 16 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 117)))))))))))))))) (allB_succ 15 117 (allA_succ_of_accept 14 15
  117 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 15 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 117 3 4 5 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 15 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 117 3 3 5 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 117 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 15 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 117 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 15 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 117 3 2 5 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 117
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 15 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 117 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 15 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 117 3 1 5 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 117
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 15 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 117))))))))))))))) (allB_succ 14 117 (allA_succ_of_accept 13 14 117 (accept_3_4 13 14 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 14 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 117
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 117 (accept_3_4 10 14 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  14 117 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 14 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 14 117 (Polychromatic418967fa.accept_19_8_14_3_1_4151 8 14 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 117 (accept_3_4 7 14 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 117 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 14 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 117
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 14 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 117 (accept_3_4 4 14 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 117 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 14 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 117 (accept_3_4 1 14 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 117)))))))))))))) (allB_succ 13 117 (allA_succ_of_accept 12 13 117
  (Polychromatic418967fa.accept_19_12_13_3_1_5447 12 13 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 117 (accept_3_5 11 13 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 117 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 13 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 117 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 13 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 117 (accept_3_5 8 13 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 117 (Polychromatic418967fa.accept_19_7_13_3_1_4171 7 13 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 117
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 13 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 117 (accept_3_5 5 13 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  117 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 117 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 13 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 117 (accept_3_5 2 13 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 117 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 13 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 117))))))))))))) (allB_succ 12 117 (allA_succ_of_accept 11 12
  117 (Polychromatic418967fa.accept_18_11_12_9_1_992 11 12 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 12 117 (Polychromatic418967fa.accept_14_10_12_5_1_3466 10 12 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 117 3 3 4 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 117
  (Polychromatic418967fa.accept_16_8_12_5_1_200 8 12 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 117 (Polychromatic418967fa.accept_14_7_12_5_1_1861 7 12 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 117 3 2 4 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 117 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 12 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 117
  (Polychromatic418967fa.accept_10_4_2_7_1_373 4 12 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 12 117 3 1 4 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 12 117 (Polychromatic418967fa.accept_19_2_12_3_1_5446 2 12 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 117 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 12 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 117)))))))))))) (allB_succ 11 117
  (allA_succ_of_accept 10 11 117 (accept_3_4 10 11 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  11 117 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 11 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 11 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 117 (accept_3_4 7 11 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 117
  (Polychromatic418967fa.accept_17_5_11_15_1_5445 5 11 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 11 117 (accept_3_4 4 11 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11
  117 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 11 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 11 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 117 (accept_3_4 1 11 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 11 117))))))))))) (allB_succ 10 117 (allA_succ_of_accept 9 10 117
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 10 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 117 (accept_3_5 8 10 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  117 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 117 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 10 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 117 (accept_3_5 5 10 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 10 117 (Polychromatic418967fa.accept_17_4_10_15_1_5444 4 10 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 117 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 117 (accept_3_5 2 10 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 117 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 10
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 117)))))))))) (allB_succ 9 117
  (allA_succ_of_accept 8 9 117 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 9 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 117 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 9 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 117 3 2 3 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 117
  (Polychromatic418967fa.accept_11_5_9_7_1_411 5 9 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 117 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 9 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 117 3 1 3 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 117 (Polychromatic418967fa.accept_10_2_9_7_1_720 2 9 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 117
  (Polychromatic418967fa.accept_16_1_9_5_1_5443 1 9 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 117))))))))) (allB_succ 8 117 (allA_succ_of_accept 7 8 117 (accept_3_4 7 8 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 117 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 8 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 117
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 117 (accept_3_4 4 8 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 117
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 8 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 117 (Polychromatic418967fa.accept_25_2_8_17_1_5442 2 8 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 117 (accept_3_4 1 8 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 117)))))))) (allB_succ 7 117 (allA_succ_of_accept 6 7 117
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 117 (accept_3_5 5 7 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 117
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 117 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 7 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 117 (accept_3_5 2 7 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 117 (Polychromatic418967fa.accept_21_1_7_12_1_1465 1 7 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 117))))))) (allB_succ 6 117 (allA_succ_of_accept 5 6 117
  (Polychromatic418967fa.accept_15_5_6_12_1_916 5 6 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 117 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 6 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 117 3 1 2 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 117 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 6 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 117
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 6 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 117)))))) (allB_succ 5 117 (allA_succ_of_accept 4 5 117 (accept_3_4 4 5 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 117 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 5 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 117 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 5
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 117 (accept_3_4 1 5 117
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 117))))) (allB_succ 4 117 (allA_succ_of_accept 3 4 117
  (Polychromatic418967fa.accept_10_3_4_7_1_353 3 4 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 117 (accept_3_5 2 4 117 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 117
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 117)))) (allB_succ 3 117 (allA_succ_of_accept 2 3 117 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 117
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 3 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 117))) (allB_succ 2 117 (allA_succ_of_accept 1 2 117 (accept_3_4 1 2 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 117)) (allB_two
  117)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


