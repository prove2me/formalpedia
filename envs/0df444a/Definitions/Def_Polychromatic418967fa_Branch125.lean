-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch125
-- name    : Polychromatic418967fa_Branch125
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:12:20.38698+00:00
-- url     : https://prove2.me/theorems/24e52064-5c7e-483e-aac0-bd4411132bb0
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

def Polychromatic418967fa.branch_125 : allB 125 125 :=
  allB_succ' 2 124 125 (Eq.refl Bool.true) (allA_of_3_0 2 124 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  123 125 (Eq.refl Bool.true) (allA_succ_of_accept 2 123 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 123 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 125 (accept_3_2 1 123 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123 125))) (allB_succ' 4 122 125 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 122 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 122 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 122 125 (accept_3_2 1 122 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122 125)))) (allB_succ' 5 121 125 (Eq.refl Bool.true) (allA_of_3_0
  5 121 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 120 125 (Eq.refl Bool.true) (allA_succ_of_gcd 5 120
  125 5 1 24 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4
  120 125 (accept_3_2 4 120 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 125
  (Polychromatic418967fa.accept_16_3_8_13_1_3867 3 120 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 120 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 120 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 125 (accept_3_2 1 120 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 120 125)))))) (allB_succ' 7 119 125 (Eq.refl Bool.true) (allA_succ_of_accept 6 119 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 119 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 119 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 119 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 125 (accept_3_2 4 119 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 119 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 119 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2
  119 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 125 (accept_3_2 1 119
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119 125))))))) (allB_succ' 8 118 125 (Eq.refl Bool.true)
  (allA_of_3_0 8 118 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 117 125 (Eq.refl Bool.true)
  (allA_succ_of_accept 8 117 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 125 (accept_3_2 7 117 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 125 (Polychromatic418967fa.accept_14_6_5_13_1_367 6 117 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 125
  (Polychromatic418967fa.accept_26_5_13_21_1_6091 5 117 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 125 (accept_3_2 4 117 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 125 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 117 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 117 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 125 (accept_3_2 1 117 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117 125))))))))) (allB_succ' 10 116 125 (Eq.refl Bool.true) (allA_succ_of_accept 9 116
  125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 116 125 (Polychromatic418967fa.accept_15_8_11_5_1_169 8 116 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 125 (accept_3_2 7 116 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 116 125 (Polychromatic418967fa.accept_15_6_11_5_1_168 6 116 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  116 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 125 (accept_3_2 4 116
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 125 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 116 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 125
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 116 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 125 (accept_3_2 1 116 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  125)))))))))) (allB_succ' 11 115 125 (Eq.refl Bool.true) (allA_of_3_0 11 115 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 114 125 (Eq.refl Bool.true) (allA_succ_of_accept 11 114 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 114 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 114 125 (accept_3_2 10 114 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  114 125 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 114 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 114 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 114 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 125 (accept_3_2 7 114 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 125 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 114 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 125
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 114 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 125 (accept_3_2 4 114 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  114 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 114 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 114 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 125 (accept_3_2 1 114 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 114 125)))))))))))) (allB_succ' 13 113 125 (Eq.refl Bool.true) (allA_succ_of_accept 12
  113 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 113 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 113 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 125 (accept_3_2 10 113 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 113 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 125
  (Polychromatic418967fa.accept_10_8_3_5_1_613 8 113 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 125 (accept_3_2 7 113 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 113 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 113 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 125 (accept_3_2 4 113 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 113 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 125
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 113 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 125 (accept_3_2 1 113 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  125))))))))))))) (allB_succ' 14 112 125 (Eq.refl Bool.true) (allA_of_3_0 14 112 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 111 125 (Eq.refl Bool.true) (allA_succ_of_accept 14 111 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 125 (accept_3_2 13 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 111 125 (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 111 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 125 (accept_3_2 10 111 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 125 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 111 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 125 (accept_3_2 7 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 111 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 125 (accept_3_2 4 111 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 125 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 111 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 125 (accept_3_2 1 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  125))))))))))))))) (allB_succ' 16 110 125 (Eq.refl Bool.true) (allA_succ_of_gcd 15 110 125 5 3 22 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 110 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 110 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 110 125 (accept_3_2 13 110 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 110 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 110 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 110 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 125 5 2 22 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 125
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 110 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 110 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 110 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 125 (accept_3_2 7 110 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 110 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 110 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 110 125 5 1 22 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 110 125 (accept_3_2 4 110 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 125
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 2 110 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 125 (accept_3_2 1 110 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  125)))))))))))))))) (allB_succ' 17 109 125 (Eq.refl Bool.true) (allA_of_3_0 17 109 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 108 125 (Eq.refl Bool.true) (allA_succ_of_accept 17 108 125
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 108 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 108 125 (accept_3_2 16 108 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 108 125 (Polychromatic418967fa.accept_16_15_12_13_1_1045 15 108 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 125 (Polychromatic418967fa.accept_20_14_8_5_1_6090 14 108 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 125 (accept_3_2 13 108 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 125 (Polychromatic418967fa.accept_10_2_8_5_1_587
  12 108 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 125
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 108 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 125 (accept_3_2 10 108 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  108 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 108 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 108 125 (Polychromatic418967fa.accept_15_8_3_5_1_608 8 108 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 125 (accept_3_2 7 108 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 125 (Polychromatic418967fa.accept_15_6_3_5_1_607 6 108 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 125
  (Polychromatic418967fa.accept_19_5_13_11_1_6089 5 108 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 125 (accept_3_2 4 108 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  108 125 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 108 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 108 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 108 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 125 (accept_3_2 1 108 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108 125)))))))))))))))))) (allB_succ' 19 107 125 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 107 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 107 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 107 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 125 (accept_3_2 16 107 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  107 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 107 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 125 (accept_3_2 13 107 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 125 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 107 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 107 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 125 (accept_3_2 10 107 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 125 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 107 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 125
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 107 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 125 (accept_3_2 7 107 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 125 (Polychromatic418967fa.accept_13_5_3_8_1_1117 5 107 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 125 (accept_3_2 4 107 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 107 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 125 (accept_3_2 1 107 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  125))))))))))))))))))) (allB_succ' 20 106 125 (Eq.refl Bool.true) (allA_of_3_0 20 106 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 105 125 (Eq.refl Bool.true) (allA_succ_of_gcd 20 105 125 5 4 21 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 125 (accept_3_2 19 105 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 125 (Polychromatic418967fa.accept_13_5_1_8_1_1115
  18 105 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 125
  (Polychromatic418967fa.accept_16_1_9_13_1_1822 17 105 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 125 (accept_3_2 16 105 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  105 125 5 3 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 105 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 105 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 105 125 (accept_3_2 13 105 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 105 125 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 105 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 105 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 105 125 5 2 21 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 105 125
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 105 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 125 (accept_3_2 7 105 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 125 (Polychromatic418967fa.accept_13_6_1_8_1_1116 6 105 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 105 125 5 1 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 125 (accept_3_2 4 105 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 105 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 105 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 125 (accept_3_2 1 105 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  125))))))))))))))))))))) (allB_succ' 22 104 125 (Eq.refl Bool.true) (allA_succ_of_accept 21 104 125
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 104 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 104 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 125 (accept_3_2 19 104 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 104 125 (Polychromatic418967fa.accept_17_1_2_6_1_818 18 104 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 125
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 104 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 125 (accept_3_2 16 104 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 125 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 104 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 125 (accept_3_2 13 104 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 104 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 125
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 104 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 125 (accept_3_2 10 104 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 125 (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 104 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 125 (accept_3_2 7 104 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 104 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 125
  (Polychromatic418967fa.accept_14_5_6_13_1_3145 5 104 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 125 (accept_3_2 4 104 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 104 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 125 (accept_3_2 1 104 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104 125)))))))))))))))))))))) (allB_succ' 23 103 125 (Eq.refl Bool.true) (allA_of_3_0
  23 103 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 102 125 (Eq.refl Bool.true) (allA_succ_of_accept 23
  102 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 102 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 102 125 (accept_3_2 22 102 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 102 125 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 102 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 102 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 125 (accept_3_2 19 102 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 125 (Polychromatic418967fa.accept_10_8_2_5_1_596
  18 102 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 125
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 102 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 125 (accept_3_2 16 102 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 102 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 102 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 102 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 125 (accept_3_2 13 102 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 102 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 102 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 125 (accept_3_2 10 102 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  102 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 102 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 102 125 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 102 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 125 (accept_3_2 7 102 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 102 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 125
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 102 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 125 (accept_3_2 4 102 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  102 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 102 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 102 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 125 (accept_3_2 1 102 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 102 125)))))))))))))))))))))))) (allB_succ' 25 101 125 (Eq.refl Bool.true)
  (allA_succ_of_accept 24 101 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 101 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 125 (accept_3_2 22 101 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 125 (Polychromatic418967fa.accept_9_3_2_8_1_108
  21 101 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 125
  (Polychromatic418967fa.accept_11_9_2_4_1_707 20 101 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 125 (accept_3_2 19 101 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 101 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 125 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 101 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 125 (accept_3_2 16 101 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 101 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 101 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 125 (accept_3_2 13 101 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 101 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 101 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 125 (accept_3_2 10 101 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 101 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 125
  (Polychromatic418967fa.accept_15_8_11_5_1_169 8 101 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 125 (accept_3_2 7 101 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 101 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 101 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 125 (accept_3_2 4 101 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 101 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 125
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 101 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 125 (accept_3_2 1 101 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  125))))))))))))))))))))))))) (allB_succ' 26 100 125 (Eq.refl Bool.true) (allA_of_3_0 26 100 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 99 125 (Eq.refl Bool.true) (allA_succ_of_accept 26 99 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 125 (accept_3_2 25 99 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 125 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 99 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 99 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 125 (accept_3_2 22 99 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 125 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 99 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 125 (accept_3_2 19 99 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 125 (Polychromatic418967fa.accept_16_1_3_13_1_2785 17 99 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 125 (accept_3_2 16 99 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 125 (Polychromatic418967fa.accept_16_15_3_13_1_2818 15 99
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 125 (accept_3_2 13 99 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 99 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 125 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 99 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 125 (accept_3_2 10 99 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 99 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 125 (accept_3_2 7 99 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 99 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 125 (accept_3_2 4 99 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 125 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 99 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 125 (accept_3_2 1 99 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 125))))))))))))))))))))))))))) (allB_succ' 28 98 125 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 98 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 125 (Polychromatic418967fa.accept_15_11_8_5_1_1278
  26 98 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 98 125 (accept_3_2 25
  98 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 98 125
  (Polychromatic418967fa.accept_17_7_13_6_1_811 24 98 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 98 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 125 (accept_3_2 22 98 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 98 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 98 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 125 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 98 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 98 125 (accept_3_2 19
  98 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 98 125
  (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 98 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 98 125 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 98 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 125 (accept_3_2 16 98 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 98 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 125 (Polychromatic418967fa.accept_13_1_7_8_1_1796
  14 98 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 98 125 (accept_3_2 13
  98 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 98 125
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 98 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 98 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 125 (accept_3_2 10 98 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 98 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 98 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 125 (Polychromatic418967fa.accept_12_8_2_5_1_844 8
  98 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 98 125 (accept_3_2 7 98 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98 125 (Polychromatic418967fa.accept_21_6_14_20_1_4594
  6 98 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 98 125
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 98 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 98 125 (accept_3_2 4 98 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 98
  125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 98 125 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 98 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 125 (accept_3_2 1 98 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 98 125)))))))))))))))))))))))))))) (allB_succ' 29 97 125 (Eq.refl Bool.true) (allA_of_3_0 29 97
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 96 125 (Eq.refl Bool.true) (allA_succ_of_accept 29 96 125
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 125 (accept_3_2 28 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  96 125 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 96 125 (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 96 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 125 (accept_3_2 25 96 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 125 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 96 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 96 125
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 125 (accept_3_2 22 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  96 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 96 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 96 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 125 (accept_3_2 19 96 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 125 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 96 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 125
  (Polychromatic418967fa.accept_22_17_8_15_1_6088 17 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 125 (accept_3_2 16 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 125 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 96 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 125 (accept_3_2 13 96 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 96 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 125
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 125 (accept_3_2 10 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  96 125 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 96 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 96 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 125 (accept_3_2 7 96 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 125 (Polychromatic418967fa.accept_14_6_12_13_1_3180 6 96 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 125
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 125 (accept_3_2 4 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  125 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 96 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 96 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 125 (accept_3_2 1 96 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96 125)))))))))))))))))))))))))))))) (allB_succ' 31 95 125 (Eq.refl Bool.true) (allA_succ_of_gcd
  30 95 125 5 6 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 95 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 95 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 125 (accept_3_2 28 95 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 95 125 (Polychromatic418967fa.accept_20_7_15_5_1_6087 27 95 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 95 125 5 5 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 95 125 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 95 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 95 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 125 (accept_3_2 22 95 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 21
  95 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 95 125 5 4 19 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 95 125 (accept_3_2 19
  95 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 95 125 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 95 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 125 (accept_3_2 16 95 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 95 125 5 3 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 95 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 125 (accept_3_2 13 95 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 95 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 125
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 95 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 95 125 5 2 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 95 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 95 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 125 (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 95 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 125 (accept_3_2 7 95 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 125 5 1 19 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 125 (accept_3_2 4 95
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 125 (Polychromatic418967fa.accept_7_3_4_6_1_329
  3 95 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 125 (accept_3_2 1 95 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  125))))))))))))))))))))))))))))))) (allB_succ' 32 94 125 (Eq.refl Bool.true) (allA_of_3_0 32 94 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 93 125 (Eq.refl Bool.true) (allA_succ_of_accept 32 93 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 125 (accept_3_2 31 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 125 (Polychromatic418967fa.accept_20_10_13_5_1_6086 30 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 93 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 125 (accept_3_2 28 93 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 125 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 93 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 125 (accept_3_2 25 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 93 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 125 (accept_3_2 22 93 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 125 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 93 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 125 (accept_3_2 19 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 93 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 125 (accept_3_2 16 93 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 93 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 125 (accept_3_2 13 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 125 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 93 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 125 (accept_3_2 10 93 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 125 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 93 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 125 (accept_3_2 7 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  125 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 93 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 93 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 125 (accept_3_2 4 93 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 93 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 93
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 125 (accept_3_2 1 93 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 125))))))))))))))))))))))))))))))))) (allB_succ' 34 92 125
  (Eq.refl Bool.true) (allA_succ_of_accept 33 92 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 125 (accept_3_2 31 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 125 (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 92 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 125 (accept_3_2 28 92 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 125
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 125 (accept_3_2 25 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 92 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 125 (accept_3_2 22 92 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 125
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 20 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 125 (accept_3_2 19 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 125 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 125 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 92 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 125 (accept_3_2 16 92 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 125 (accept_3_2 13 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 125 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 92 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 125 (accept_3_2 10 92 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 125
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 125 (accept_3_2 7 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  125 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 92 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 92 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 125 (accept_3_2 4 92 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  92 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 125 (accept_3_2 1 92 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92 125)))))))))))))))))))))))))))))))))) (allB_succ' 35 91 125
  (Eq.refl Bool.true) (allA_of_3_0 35 91 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 90 125 (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 90 125 5 7 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 90 125 (accept_3_2 34 90 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 90 125 (Polychromatic418967fa.accept_13_7_12_8_1_199 33 90 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 125 (Polychromatic418967fa.accept_20_12_10_5_1_4661 32 90
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 125 (accept_3_2 31 90 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 125 5 6 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 125 (Polychromatic418967fa.accept_20_9_10_5_1_6085
  29 90 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 125 (accept_3_2 28
  90 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 90 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 90 125 (Polychromatic418967fa.accept_14_12_6_13_1_3173 26 90 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 90 125 5 5 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 90 125 (Polychromatic418967fa.accept_19_5_14_11_1_6084 24 90
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 125 (accept_3_2 22 90 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  90 125 (Polychromatic418967fa.accept_14_7_6_13_1_4111 21 90 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 90 125 5 4 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 90 125 (accept_3_2 19 90 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 90 125 (Polychromatic418967fa.accept_13_5_12_8_1_198 18 90 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 125 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 90 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 125 (accept_3_2 16 90 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 125 5 3 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 125 (Polychromatic418967fa.accept_13_1_12_8_1_1818
  14 90 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 125 (accept_3_2 13
  90 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 125
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 90 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 90 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 125 5 2 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 125 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 90 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 125
  (Polychromatic418967fa.accept_20_8_10_5_1_6083 8 90 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 90 125 (accept_3_2 7 90 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90
  125 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 90 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 90 125 5 1 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 90 125 (accept_3_2 4 90 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 90 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 125 (Polychromatic418967fa.accept_20_2_10_5_1_6082 2 90 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 125 (accept_3_2 1 90 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90 125)))))))))))))))))))))))))))))))))))) (allB_succ' 37 89 125
  (Eq.refl Bool.true) (allA_succ_of_accept 36 89 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 89 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 125
  (Polychromatic418967fa.accept_13_9_11_8_1_195 35 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 125 (accept_3_2 34 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 125 (Polychromatic418967fa.accept_16_1_9_13_1_1822 33 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 125 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 89 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 125 (accept_3_2 31 89 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 125 (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 89 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 125
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 125 (accept_3_2 28 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 125 (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 125 (Polychromatic418967fa.accept_10_6_9_5_1_1046 26 89 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 125 (accept_3_2 25 89 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 125 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 89 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 125
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 23 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 125 (accept_3_2 22 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 125 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 125 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 89 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 125 (accept_3_2 19 89 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 125 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 89 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 125
  (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 125 (accept_3_2 16 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 125 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 89 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 125 (accept_3_2 13 89 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 125 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 89 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 125
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 125 (accept_3_2 10 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 125 (Polychromatic418967fa.accept_13_9_11_8_1_195 9 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 89 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 125 (accept_3_2 7 89 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 125 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 89 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 125
  (Polychromatic418967fa.accept_16_5_9_13_1_3845 5 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 125 (accept_3_2 4 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  125 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 89 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 89 125 (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 89 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 125 (accept_3_2 1 89 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 89 125))))))))))))))))))))))))))))))))))))) (allB_succ' 38 88 125 (Eq.refl Bool.true)
  (allA_of_3_0 38 88 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 87 125 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 87 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 125 (accept_3_2 37 87 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 125 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 87 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 125
  (Polychromatic418967fa.accept_17_1_2_6_1_818 35 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 125 (accept_3_2 34 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 125 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 125 (accept_3_2 31 87 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 125
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 125 (accept_3_2 28 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 125 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 125 (accept_3_2 25 87 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 125 (Polychromatic418967fa.accept_13_11_9_8_1_1125 24 87 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 125
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 125 (accept_3_2 22 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 125 (accept_3_2 19 87 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 125
  (Polychromatic418967fa.accept_13_4_9_8_1_1736 17 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 125 (accept_3_2 16 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 125 (Polychromatic418967fa.accept_20_15_7_5_1_2115 15 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 125 (accept_3_2 13 87 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 87 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 125
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 125 (accept_3_2 10 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 125 (accept_3_2 7 87 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 87 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 125 (Polychromatic418967fa.accept_9_5_6_8_1_101 5
  87 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 125 (accept_3_2 4 87 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  87 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 125 (accept_3_2 1 87 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  125))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 86 125 (Eq.refl Bool.true) (allA_succ_of_accept 39 86 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 86 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 86 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 86 125 (accept_3_2 37 86 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 86 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 86 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 86 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  86 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 125 (accept_3_2 34 86
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 125 (Polychromatic418967fa.accept_6_3_2_5_1_32
  33 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 125
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 125 (accept_3_2 31 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 86 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 125 (accept_3_2 28 86 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 125
  (Polychromatic418967fa.accept_21_5_2_20_1_6081 26 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 125 (accept_3_2 25 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 125 (accept_3_2 22 86 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 86 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 125
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 125 (accept_3_2 19 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 86 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 125 (accept_3_2 16 86 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 125
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 125 (accept_3_2 13 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 125 (accept_3_2 10 86 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 86 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 125
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 125 (accept_3_2 7 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  125 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 86 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 125 (Polychromatic418967fa.accept_17_5_1_6_1_2615 5 86 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 125 (accept_3_2 4 86 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 86
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 125 (accept_3_2 1 86 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86 125)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 85
  125 (Eq.refl Bool.true) (allA_of_3_0 41 85 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 84 125 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 84 125 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 84 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 125 (accept_3_2 40 84 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 84 125 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 84 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 125
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 84 125 (accept_3_2 37 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  84 125 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 84 125 (Polychromatic418967fa.accept_19_16_8_11_1_6080 35 84 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 125 (accept_3_2 34 84 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 84 125 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 84 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 125
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 84 125 (accept_3_2 31 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  84 125 (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 84 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 84 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 125 (accept_3_2 28 84 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 84 125 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 84 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 125
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 125 (accept_3_2 25 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  84 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 84 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 84 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 125 (accept_3_2 22 84 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 84 125 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 84 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 125
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 84 125 (accept_3_2 19 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  84 125 (Polychromatic418967fa.accept_15_3_9_5_1_2082 18 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 84 125 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 84 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 125 (accept_3_2 16 84 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 84 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 84 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 125
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 84 125 (accept_3_2 13 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  84 125 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 84 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 125 (accept_3_2 10 84 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 84 125 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 84 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 125
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 84 125 (accept_3_2 7 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84
  125 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 84 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 125 (accept_3_2 4 84 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 84 125 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 84 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  84 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 125 (accept_3_2 1 84 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 125)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 83
  125 (Eq.refl Bool.true) (allA_succ_of_accept 42 83 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 125 (accept_3_2 40 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 125 (accept_3_2 37 83 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 125 (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 83 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 125
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 125 (accept_3_2 34 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 83 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 125 (accept_3_2 31 83 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 125
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 29 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 125 (accept_3_2 28 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 125 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 125 (accept_3_2 25 83 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 83 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 125 (accept_3_2 22 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 125 (Polychromatic418967fa.accept_18_2_11_17_1_4773 20 83 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 125 (accept_3_2 19 83 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 125
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 125 (accept_3_2 16 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 125 (accept_3_2 13 83 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 83 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 125
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 125 (accept_3_2 10 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 125 (Polychromatic418967fa.accept_17_9_15_6_1_3744 9 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 125 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 83 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 125 (accept_3_2 7 83 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 125 (accept_3_2 4 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  125 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 83 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 125 (accept_3_2 1 83 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 125))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 82 125 (Eq.refl Bool.true)
  (allA_of_3_0 44 82 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 81 125 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 125 (accept_3_2 43 81 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 125 (Polychromatic418967fa.accept_15_12_6_5_1_1275 42 81 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 125
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 41 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 125 (accept_3_2 40 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 125 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 81 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 125 (accept_3_2 37 81 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 125 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 81 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 125
  (Polychromatic418967fa.accept_13_9_3_8_1_573 35 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 125 (accept_3_2 34 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 125 (accept_3_2 31 81 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 81 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 125
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 125 (accept_3_2 28 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 125 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 81 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 125 (accept_3_2 25 81 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 125 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 81 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 125
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 125 (accept_3_2 22 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 125 (Polychromatic418967fa.accept_16_5_1_13_1_1053 21 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 125 (accept_3_2 19 81 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 125 (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 81 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 125
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 125 (accept_3_2 16 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 125 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 81 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 125 (accept_3_2 13 81 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 81 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 125
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 11 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 125 (accept_3_2 10 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 125 (accept_3_2 7 81 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 125 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 81 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 125
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 125 (accept_3_2 4 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  125 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 81 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 125 (accept_3_2 1 81 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 125))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 80 125 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 80 125 5 9 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 80 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 80 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 80 125 (accept_3_2 43 80 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 80 125 (Polychromatic418967fa.accept_26_16_2_21_1_6079 42 80 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 80 125
  (Polychromatic418967fa.accept_18_5_8_17_1_3478 41 80 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 80 125 5 8 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 125 (Polychromatic418967fa.accept_12_2_8_5_1_408 38 80 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 80 125 (accept_3_2 37 80 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 80 125 (Polychromatic418967fa.accept_13_10_2_8_1_2603
  36 80 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 80 125 5 7 16 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 80 125 (accept_3_2 34
  80 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 125
  (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 80 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 80 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 80 125 (accept_3_2 31 80 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 80 125 5 6 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 80 125 (Polychromatic418967fa.accept_11_7_3_4_1_729 29 80 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 125 (accept_3_2 28 80 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 125
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 80 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 80 125 5 5 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 80 125 (Polychromatic418967fa.accept_21_3_17_20_1_3162 24 80 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 80 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 80 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 125 (accept_3_2 22 80 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  80 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 125 5 4 16 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 125 (accept_3_2 19
  80 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 125
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 80 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 80 125 (Polychromatic418967fa.accept_14_3_10_13_1_339 17 80 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 125 (accept_3_2 16 80 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 80 125 5 3 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 80 125 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 80 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 80 125 (accept_3_2 13 80 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 80 125 (Polychromatic418967fa.accept_19_12_4_11_1_6078 12 80 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 125
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 80 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 80 125 5 2 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 80 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 125 (Polychromatic418967fa.accept_21_8_17_20_1_3142 8 80 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 125 (accept_3_2 7 80 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 125 (Polychromatic418967fa.accept_13_6_2_8_1_1782 6
  80 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 80 125 5 1 16 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 80 125 (accept_3_2 4 80
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 125 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 80 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 125
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 80 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 125 (accept_3_2 1 80 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  125)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 79 125 (Eq.refl Bool.true) (allA_of_3_0 47 79 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 78 125 (Eq.refl Bool.true) (allA_succ_of_accept 47 78 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 125 (accept_3_2 46 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 125 (Polychromatic418967fa.accept_22_1_12_15_1_6077 45 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 78 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 125 (accept_3_2 43 78 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 125 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 78 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 125
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 125 (accept_3_2 40 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 78 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 125 (accept_3_2 37 78 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 125 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 78 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 125 (accept_3_2 34 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 125 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 78 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 125 (accept_3_2 31 78 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 78 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 125
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 125 (accept_3_2 28 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 78 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 125 (accept_3_2 25 78 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 125 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 78 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 125 (accept_3_2 22 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 78 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 125 (accept_3_2 19 78 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 125 (Polychromatic418967fa.accept_21_18_15_20_1_6076 18 78 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 125
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 125 (accept_3_2 16 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 125 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 78 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 125 (accept_3_2 13 78 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 78 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 125 (accept_3_2 10 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 78 125 (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 78 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 125 (accept_3_2 7 78 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 125 (Polychromatic418967fa.accept_15_6_3_5_1_607 6 78 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 125
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 125 (accept_3_2 4 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78
  125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 78 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 78 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 125 (accept_3_2 1 78 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 125)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 77 125 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 77 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 77 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 125 (accept_3_2 46 77 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 77 125
  (Polychromatic418967fa.accept_22_1_11_15_1_6075 45 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 77 125 (Polychromatic418967fa.accept_13_5_12_8_1_198 44 77 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 125 (accept_3_2 43 77 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 77 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 77 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 125 (Polychromatic418967fa.accept_15_11_2_5_1_2076
  41 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 77 125 (accept_3_2 40
  77 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 77 125
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 77 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 77 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 125 (accept_3_2 37 77 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 77 125 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 77 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 125
  (Polychromatic418967fa.accept_13_9_12_8_1_570 35 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 125 (accept_3_2 34 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 125 (Polychromatic418967fa.accept_10_2_7_5_1_605 32 77 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 125 (accept_3_2 31 77 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 77 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 125
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 125 (accept_3_2 28 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 125 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 125 (Polychromatic418967fa.accept_15_11_2_5_1_2076 26 77 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 125 (accept_3_2 25 77 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 125
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 125 (accept_3_2 22 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 125 (accept_3_2 19 77 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 125 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 77 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 125
  (Polychromatic418967fa.accept_13_4_12_8_1_197 17 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 125 (accept_3_2 16 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 125 (Polychromatic418967fa.accept_13_1_12_8_1_1818 14 77 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 125 (accept_3_2 13 77 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 125
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 125 (accept_3_2 10 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 125 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 125 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 77 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 125 (accept_3_2 7 77 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 77 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 125
  (Polychromatic418967fa.accept_13_5_12_8_1_198 5 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 125 (accept_3_2 4 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  125 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 77 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 77 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 125 (accept_3_2 1 77 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 125))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 76 125 (Eq.refl
  Bool.true) (allA_of_3_0 50 76 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 75 125 (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 75 125 25 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 75 125 (accept_3_2 49 75 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 125 (Polychromatic418967fa.accept_14_6_5_13_1_367 48 75 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 75 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 125 (accept_3_2 46 75 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 125 5 9 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 75 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 125 (accept_3_2 43 75 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 125
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 75 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 75 125 5 8 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 75 125 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 75 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 125 (accept_3_2 37 75 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 36
  75 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 75 125 5 7 15 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 75 125 (accept_3_2 34
  75 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 125
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 75 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 125 (accept_3_2 31 75 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 75 125 5 6 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 75 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 75 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 125 (accept_3_2 28 75 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 125 (Polychromatic418967fa.accept_19_8_18_11_1_3408 27 75 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 75 125 25 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 75 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 75 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 75 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 125 (accept_3_2 22 75 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 125 (Polychromatic418967fa.accept_12_9_3_5_1_423
  21 75 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 75 125 5 4 15 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 125 (accept_3_2 19
  75 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 125 (Polychromatic418967fa.accept_13_4_10_8_1_1817 17 75 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 125 (accept_3_2 16 75 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 75 125 5 3 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 75 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 125 (accept_3_2 13 75 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 125 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 75 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 125
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 75 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 75 125 5 2 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 75 125 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 75 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 125 (accept_3_2 7 75 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 75 125 5 1 15 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 125 (accept_3_2 4 75
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 125
  (Polychromatic418967fa.accept_19_3_18_11_1_6074 3 75 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 75 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 125 (accept_3_2 1 75 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 75 125))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 74 125 (Eq.refl
  Bool.true) (allA_succ_of_accept 51 74 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 50
  74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 125 (accept_3_2 49 74
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 125
  (Polychromatic418967fa.accept_9_3_2_8_1_108 48 74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 74 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 125 (accept_3_2 46 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 74 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 74 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 44
  74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 125 (accept_3_2 43 74
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 125
  (Polychromatic418967fa.accept_9_6_2_8_1_592 42 74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 74 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 125 (accept_3_2 40 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 74 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 125 (Polychromatic418967fa.accept_7_3_4_6_1_329 38
  74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 74 125 (accept_3_2 37 74
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 74 125
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 74 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 125 (accept_3_2 34 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 74 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 74 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 32
  74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 125 (accept_3_2 31 74
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 125
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 74 125 (Polychromatic418967fa.accept_10_9_4_5_1_616 29 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 125 (accept_3_2 28 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 74 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 26
  74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 125 (accept_3_2 25 74
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 125
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 74 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 125 (accept_3_2 22 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 74 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 74 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 125 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 125 (accept_3_2 19
  74 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 125
  (Polychromatic418967fa.accept_11_7_8_4_1_718 18 74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 74 125 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 125 (accept_3_2 16 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 74 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 14
  74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 125 (accept_3_2 13 74
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 125
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 74 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 125 (accept_3_2 10 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 74 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 125 (Polychromatic418967fa.accept_12_8_2_5_1_844 8
  74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 125 (accept_3_2 7 74 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 125
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 125 (accept_3_2 4 74 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74
  125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 125 (accept_3_2 1 74 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 125)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 73 125 (Eq.refl
  Bool.true) (allA_of_3_0 53 73 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 72 125 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 72 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 125 (accept_3_2 52 72 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 72 125 (Polychromatic418967fa.accept_13_12_7_8_1_1104 51 72 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 125
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 125 (accept_3_2 49 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  72 125 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 72 125 (Polychromatic418967fa.accept_10_7_2_5_1_298 47 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 125 (accept_3_2 46 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 72 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 72 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 125
  (Polychromatic418967fa.accept_16_12_8_13_1_6073 44 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 72 125 (accept_3_2 43 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  72 125 (Polychromatic418967fa.accept_13_3_7_8_1_4192 42 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 72 125 (Polychromatic418967fa.accept_13_2_7_8_1_4221 41 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 72 125 (accept_3_2 40 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 72 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 72 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 125
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 72 125 (accept_3_2 37 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  72 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 72 125 (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 125 (accept_3_2 34 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 72 125 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 72 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 125
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 125 (accept_3_2 31 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  72 125 (Polychromatic418967fa.accept_20_10_12_5_1_4687 30 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 72 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 125 (accept_3_2 28 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 72 125 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 72 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 125
  (Polychromatic418967fa.accept_19_7_15_11_1_3420 26 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 72 125 (accept_3_2 25 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  72 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 72 125 (Polychromatic418967fa.accept_10_3_2_5_1_295 23 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 125 (accept_3_2 22 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 72 125 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 72 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 125
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 20 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 72 125 (accept_3_2 19 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  72 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 72 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 125 (accept_3_2 16 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 72 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 72 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 125
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 14 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 125 (accept_3_2 13 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  72 125 (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 72 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 125 (accept_3_2 10 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 72 125 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 72 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 125
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 72 125 (accept_3_2 7 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72
  125 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 72 125 (Polychromatic418967fa.accept_16_5_8_13_1_2764 5 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 125 (accept_3_2 4 72 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 72 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 125
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 72 125 (accept_3_2 1 72 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  125)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 71 125 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 71 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 125 (Polychromatic418967fa.accept_13_1_6_8_1_208 53 71 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 125 (accept_3_2 52 71 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 51
  71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 71 125 (accept_3_2 49 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  71 125 (Polychromatic418967fa.accept_17_14_3_6_1_3716 48 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 71 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 125 (accept_3_2 46 71 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 125 (Polychromatic418967fa.accept_19_7_14_11_1_4724 45 71 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 125
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 125 (accept_3_2 43 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 125 (Polychromatic418967fa.accept_13_2_6_8_1_1092 41 71 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 125 (accept_3_2 40 71 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 125 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 71 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 125 (accept_3_2 37 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 125 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 125 (Polychromatic418967fa.accept_14_7_1_13_1_357 35 71 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 125 (accept_3_2 34 71 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 71 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 125
  (Polychromatic418967fa.accept_11_10_5_4_1_711 32 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 125 (accept_3_2 31 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 125 (Polychromatic418967fa.accept_10_9_1_5_1_594 29 71 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 125 (accept_3_2 28 71 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 125 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 71 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 125 (accept_3_2 25 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 125 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 71 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 125 (accept_3_2 22 71 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 125 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 71 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 125
  (Polychromatic418967fa.accept_16_4_7_13_1_2795 20 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 125 (accept_3_2 19 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 125 (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 71 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 125 (accept_3_2 16 71 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 125 (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 71 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 125 (accept_3_2 13 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 125 (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 71 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 125 (accept_3_2 10 71 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 71 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 125
  (Polychromatic418967fa.accept_15_8_11_5_1_169 8 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 125 (accept_3_2 7 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 71 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 125 (accept_3_2 4 71 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 125 (Polychromatic418967fa.accept_19_3_14_11_1_2214 3 71 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 125 (accept_3_2 1 71 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71 125)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 70 125 (Eq.refl Bool.true) (allA_of_3_0 56 70 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  57 69 125 (Eq.refl Bool.true) (allA_succ_of_accept 56 69 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 125 (accept_3_2 55 69 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 125 (Polychromatic418967fa.accept_10_4_9_5_1_84 54
  69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 125
  (Polychromatic418967fa.accept_17_2_1_6_1_3777 53 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 69 125 (accept_3_2 52 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  69 125 (Polychromatic418967fa.accept_10_1_9_5_1_83 51 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 69 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 125 (accept_3_2 49 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 125
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 125 (accept_3_2 46 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  69 125 (Polychromatic418967fa.accept_18_9_15_17_1_3497 45 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 69 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 125 (accept_3_2 43 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 125 (Polychromatic418967fa.accept_15_12_9_5_1_2973 42 69 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 125
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 125 (accept_3_2 40 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  69 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 69 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 125 (accept_3_2 37 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 125 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 69 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 125
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 35 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 125 (accept_3_2 34 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  69 125 (Polychromatic418967fa.accept_15_3_9_5_1_2082 33 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 69 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 125 (accept_3_2 31 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 69 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 125
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 125 (accept_3_2 28 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  69 125 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 69 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 125 (accept_3_2 25 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 125 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 69 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 125
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 125 (accept_3_2 22 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  69 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 69 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 125 (accept_3_2 19 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 125 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 69 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 125
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 125 (accept_3_2 16 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  69 125 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 125 (accept_3_2 13 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 69 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 125
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 125 (accept_3_2 10 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  69 125 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 69 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 125 (accept_3_2 7 69 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 125 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 69 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 125
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 125 (accept_3_2 4 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69
  125 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 69 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 125 (accept_3_2 1 69 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 69 125))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 68 125 (Eq.refl
  Bool.true) (allA_succ_of_accept 57 68 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 56
  68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 125 (accept_3_2 55 68
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 125
  (Polychromatic418967fa.accept_16_6_4_13_1_3841 54 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 125 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 68 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 125 (accept_3_2 52 68 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 50
  68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 125 (accept_3_2 49 68
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 125 (Polychromatic418967fa.accept_9_3_5_8_1_99
  48 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 68 125
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 68 125 (accept_3_2 46 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  68 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 68 125 (Polychromatic418967fa.accept_13_5_3_8_1_1117 44 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 125 (accept_3_2 43 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 68 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 68 125
  (Polychromatic418967fa.accept_8_1_4_5_1_48 41 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 68 125 (accept_3_2 40 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  68 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 68 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 125 (accept_3_2 37 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 68 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 68 125
  (Polychromatic418967fa.accept_13_9_3_8_1_573 35 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 68 125 (accept_3_2 34 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  68 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 68 125 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 125 (accept_3_2 31 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 68 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 68 125
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 68 125 (accept_3_2 28 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  68 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 68 125 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 125 (accept_3_2 25 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 68 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 68 125
  (Polychromatic418967fa.accept_10_3_8_5_1_606 23 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 68 125 (accept_3_2 22 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  68 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 68 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 125 (accept_3_2 19 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 125 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 68 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 68 125
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 68 125 (accept_3_2 16 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  68 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 68 125 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 125 (accept_3_2 13 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 68 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 68 125
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 68 125 (accept_3_2 10 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  68 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 68 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 125 (accept_3_2 7 68 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 68 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 125
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 5 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 125 (accept_3_2 4 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68
  125 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 68 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 125 (accept_3_2 1 68 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 125)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 67 125 (Eq.refl
  Bool.true) (allA_of_3_0 59 67 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 66 125 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 125 (accept_3_2 58 66 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 66 125 (Polychromatic418967fa.accept_13_5_1_8_1_1115 57 66 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 66 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 56
  66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 125 (accept_3_2 55 66
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 125
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 66 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 66 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 125 (accept_3_2 52 66 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 66 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 66 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 50
  66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 125 (accept_3_2 49 66
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 125
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 48 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 66 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 125 (accept_3_2 46 66 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 66 125 (Polychromatic418967fa.accept_13_6_1_8_1_1116 45 66 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 66 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 44
  66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 125 (accept_3_2 43 66
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 125
  (Polychromatic418967fa.accept_9_6_3_8_1_595 42 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 66 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 66 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 125 (accept_3_2 40 66 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 66 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 38
  66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 125 (accept_3_2 37 66
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 125
  (Polychromatic418967fa.accept_19_17_9_11_1_6057 36 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 66 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 125 (accept_3_2 34 66 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 66 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 66 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 32
  66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 125 (accept_3_2 31 66
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 125 (Polychromatic418967fa.accept_7_2_3_6_1_4
  30 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 125
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 125 (accept_3_2 28 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 125 (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 66 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 125 (accept_3_2 25 66 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 66 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 125 (accept_3_2 22 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 125 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 66 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 125 (accept_3_2 19 66 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 66 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 125
  (Polychromatic418967fa.accept_14_3_10_13_1_339 17 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 125 (accept_3_2 16 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 66 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 125 (accept_3_2 13 66 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 125 (Polychromatic418967fa.accept_13_12_1_8_1_1779 12 66 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 125 (accept_3_2 10 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 125 (Polychromatic418967fa.accept_17_8_15_6_1_4889 8 66 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 125 (accept_3_2 7 66 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 66 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 66 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 5
  66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 125 (accept_3_2 4 66 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 125
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 125 (accept_3_2 1 66 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  125)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 65 125 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 65 125 5 12 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 65 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 65 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 125 (accept_3_2 58 65 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 65 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 65 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 125
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 56 65 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 65 125 5 11 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 65 125 (Polychromatic418967fa.accept_17_3_14_6_1_3742 54 65 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 65 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 125 (accept_3_2 52 65 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 51
  65 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 65 125 5 10 13 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 65 125 (accept_3_2 49
  65 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 125
  (Polychromatic418967fa.accept_9_3_2_8_1_108 48 65 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 65 125 (Polychromatic418967fa.accept_19_9_8_11_1_6072 47 65 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 125 (accept_3_2 46 65 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 65 125 5 9 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 65 125 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 65 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 125 (accept_3_2 43 65 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 65 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 65 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 65 125 5 8 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 65 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 65 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 65 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 125 (accept_3_2 37 65 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 36
  65 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 65 125 5 7 13 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 65 125 (accept_3_2 34
  65 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 125
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 65 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 65 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 65 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 125 (accept_3_2 31 65 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 65 125 5 6 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 65 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 65 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 125 (accept_3_2 28 65 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 125 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 65 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 125
  (Polychromatic418967fa.accept_19_7_8_11_1_3379 26 65 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 65 125 5 5 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 65 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 65 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 65 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 125 (accept_3_2 22 65 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 21
  65 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 65 125 5 4 13 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 65 125 (accept_3_2 19
  65 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 125
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 65 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 65 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 125 (accept_3_2 16 65 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 65 125 5 3 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 65 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 65 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 125 (accept_3_2 13 65 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 125 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 65 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 125
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 65 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 65 125 5 2 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 65 125 (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 65 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 65 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 125 (accept_3_2 7 65 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  65 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 125 5 1 13 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 125 (accept_3_2 4 65
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 125 (Polychromatic418967fa.accept_7_3_2_6_1_56
  3 65 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 125
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 2 65 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 125 (accept_3_2 1 65 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  125))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 64 125 (Eq.refl Bool.true)
  (allA_of_3_0 62 64 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 125 (allA_succ_of_accept 62 63 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 125 (accept_3_2 61 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 125 (Polychromatic418967fa.accept_16_12_15_13_1_3872 60 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 125 (Polychromatic418967fa.accept_27_5_9_17_1_6071 59 63 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 125 (accept_3_2 58 63 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 125 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 63 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 125 (accept_3_2 55 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 125 (Polychromatic418967fa.accept_13_1_11_8_1_2562 53 63 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 125 (accept_3_2 52 63 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 125 (Polychromatic418967fa.accept_11_7_8_4_1_718 51 63 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 125 (accept_3_2 49 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 125 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 125 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 63 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 125 (accept_3_2 46 63 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 125 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 63 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 125 (accept_3_2 43 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 125 (Polychromatic418967fa.accept_20_1_3_5_1_1060 41 63 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 125 (accept_3_2 40 63 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 125 (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 63 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 125 (accept_3_2 37 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 125 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 125 (Polychromatic418967fa.accept_13_9_11_8_1_195 35 63 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 125 (accept_3_2 34 63 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 125 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 63 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 125 (accept_3_2 31 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 125 (Polychromatic418967fa.accept_11_7_8_4_1_718 29 63 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 125 (accept_3_2 28 63 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 125 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 63 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 125 (accept_3_2 25 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 125 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 125 (Polychromatic418967fa.accept_11_1_8_4_1_717 23 63 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 125 (accept_3_2 22 63 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 125 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 63 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 125 (accept_3_2 19 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 125 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 63 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 125 (accept_3_2 16 63 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 125 (Polychromatic418967fa.accept_14_1_7_13_1_333 15 63 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 125 (accept_3_2 13 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 125 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 125 (Polychromatic418967fa.accept_17_11_12_6_1_6070 11 63 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 125 (accept_3_2 10 63 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 125 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 63 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 125 (accept_3_2 7 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 125 (Polychromatic418967fa.accept_19_5_6_11_1_6069 5 63 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 125 (accept_3_2 4 63 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 125 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 63 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 125 (accept_3_2 1 63 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  125))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 125 (allA_succ_of_accept 61 62 125
  (accept_3_2 61 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 125
  (Polychromatic418967fa.accept_26_8_10_21_1_6068 60 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 125 (accept_3_2 58 62 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 125 (Polychromatic418967fa.accept_12_8_2_5_1_844
  56 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 125 (accept_3_2 55
  62 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 125
  (Polychromatic418967fa.accept_13_2_10_8_1_1126 54 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 125 (Polychromatic418967fa.accept_10_3_2_5_1_295 53 62 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 125 (accept_3_2 52 62 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 125
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 50 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 125 (accept_3_2 49 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 125 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 125 (accept_3_2 46 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 62 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 125
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 125 (accept_3_2 43 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 125 (Polychromatic418967fa.accept_15_12_2_5_1_3939 42 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 125 (Polychromatic418967fa.accept_11_8_7_4_1_3011 41 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 125 (accept_3_2 40 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 125
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 125 (accept_3_2 37 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 125 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 125 (accept_3_2 34 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 62 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 125
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 125 (accept_3_2 31 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 125 (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 125 (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 62 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 125 (accept_3_2 28 62 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 125
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 26 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 125 (accept_3_2 25 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 125 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 125 (accept_3_2 22 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 62 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 125
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 125 (accept_3_2 19 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 125 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 125 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 125 (accept_3_2 16 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 125
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 125 (accept_3_2 13 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 125 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 125 (accept_3_2 10 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 125
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 125 (accept_3_2 7 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  125 (Polychromatic418967fa.accept_19_6_5_11_1_6067 6 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 62 125 (Polychromatic418967fa.accept_13_5_10_8_1_1127 5 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 125 (accept_3_2 4 62 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 62 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 125
  (Polychromatic418967fa.accept_13_2_10_8_1_1126 2 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 62 125 (accept_3_2 1 62 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  125)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 125 (allA_of_3_0 61 61 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 125 (allA_succ_of_accept 59 60 125
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 125 (accept_3_2 58 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 125 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 60 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 60 125 5 11 12 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 60 125
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 125 (Polychromatic418967fa.accept_21_11_18_20_1_1877 53 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 125 (accept_3_2 52 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 60 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 125 5 10 12 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 125 (accept_3_2 49 60 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 60 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 125
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 125 (accept_3_2 46 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60
  125 5 9 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  60 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 60 125 (accept_3_2 43 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 60 125 (Polychromatic418967fa.accept_16_10_12_13_1_4950 42 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 125 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 60 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 125 5 8 12 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 125
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 60 125 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 125 (accept_3_2 37 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 60 125 (Polychromatic418967fa.accept_16_4_12_13_1_990 36 60 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 60 125 5 7 12 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 60 125 (accept_3_2 34 60 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 125
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 60 125 (accept_3_2 31 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  125 5 6 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 60 125 (accept_3_2 28 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 60 125 (Polychromatic418967fa.accept_19_8_3_11_1_6048 27 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 60 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 60 125 5 5 12 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 60 125
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 125 (accept_3_2 22 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 125 5 4 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 125 (accept_3_2 19 60 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 125 (Polychromatic418967fa.accept_19_18_3_11_1_6066 18 60 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 125
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 125 (accept_3_2 16 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60
  125 5 3 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  60 125 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 60 125 (accept_3_2 13 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 60 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 125 5 2 12 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 125
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 60 125 (Polychromatic418967fa.accept_16_8_12_13_1_3851 8 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 125 (accept_3_2 7 60 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 60 125 (Polychromatic418967fa.accept_21_6_18_20_1_6065 6 60 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 60 125 5 1 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 60 125 (accept_3_2 4 60 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 125 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 125
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 60 125 (accept_3_2 1 60 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  125)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 125 (allA_succ_of_accept 58 59 125
  (accept_3_2 58 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 125
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 125 (accept_3_2 55 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 53
  59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 125 (accept_3_2 52 59
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 125 (Polychromatic418967fa.accept_7_2_3_6_1_4
  51 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 125 (accept_3_2 49 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 125 (accept_3_2 46 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 125 (Polychromatic418967fa.accept_21_3_17_20_1_3162 45 59 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 125
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 125 (accept_3_2 43 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 125 (Polychromatic418967fa.accept_10_1_9_5_1_83 41 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 125 (accept_3_2 40 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 59 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 125 (accept_3_2 37 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 125 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 125 (Polychromatic418967fa.accept_13_9_7_8_1_1122 35 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 125 (accept_3_2 34 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 59 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 125
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 125 (accept_3_2 31 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 125 (accept_3_2 28 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 125 (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 59 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 125 (accept_3_2 25 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 125 (accept_3_2 22 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 59 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 125
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 125 (accept_3_2 19 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 125 (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 59 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 125 (accept_3_2 16 59 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 59 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 125 (accept_3_2 13 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 125 (accept_3_2 10 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 59 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 125
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 125 (accept_3_2 7 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 125 (Polychromatic418967fa.accept_26_5_7_21_1_6064 5 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 125 (accept_3_2 4 59 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 59 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 125 (accept_3_2 1 59 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 125)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 58 125 (allA_of_3_0 58 58 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 125
  (allA_succ_of_accept 56 57 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 125 (accept_3_2 55 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 57 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 125 (Polychromatic418967fa.accept_10_3_7_5_1_288
  53 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 125 (accept_3_2 52
  57 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 125
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 57 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 125 (accept_3_2 49 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 57 125 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 47
  57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 125 (accept_3_2 46 57
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 125
  (Polychromatic418967fa.accept_23_22_11_10_1_6063 45 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 57 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 125 (accept_3_2 43 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 57 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 125
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 57 125 (accept_3_2 40 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  57 125 (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 57 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 125 (accept_3_2 37 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 125 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 57 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 125
  (Polychromatic418967fa.accept_14_7_1_13_1_357 35 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 57 125 (accept_3_2 34 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  57 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 57 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 125 (accept_3_2 31 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 57 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 125
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 125 (accept_3_2 28 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  57 125 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 57 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 125 (accept_3_2 25 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 57 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 125
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 125 (accept_3_2 22 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  57 125 (Polychromatic418967fa.accept_14_7_1_13_1_357 21 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 57 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 125 (accept_3_2 19 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 125 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 57 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 125
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 125 (accept_3_2 16 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  57 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 57 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 125 (accept_3_2 13 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 125
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 125 (accept_3_2 10 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  57 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 57 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 125 (accept_3_2 7 57 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 57 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 125
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 125 (accept_3_2 4 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57
  125 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 57 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 57 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 125 (accept_3_2 1 57 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 57 125))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 125
  (allA_succ_of_accept 55 56 125 (accept_3_2 55 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  56 125 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 56 125 (Polychromatic418967fa.accept_15_8_11_5_1_169 53 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 125 (accept_3_2 52 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 56 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 125 (accept_3_2 49 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 125 (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 56 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 125 (accept_3_2 46 56 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 125
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 125 (accept_3_2 43 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 125 (accept_3_2 40 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 125
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 125 (accept_3_2 37 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 125 (Polychromatic418967fa.accept_13_10_4_8_1_2570 36 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 125 (Polychromatic418967fa.accept_13_9_4_8_1_1752 35 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 125 (accept_3_2 34 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 125 (accept_3_2 31 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 125 (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 125 (accept_3_2 28 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 125
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 125 (accept_3_2 25 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 125 (accept_3_2 22 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 125
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 20 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 125 (accept_3_2 19 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 125 (Polychromatic418967fa.accept_17_1_5_6_1_3717 18 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 125 (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 56 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 125 (accept_3_2 16 56 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 125 (accept_3_2 13 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 125 (Polychromatic418967fa.accept_10_1_6_5_1_304 11 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 125 (accept_3_2 10 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 125
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 125 (accept_3_2 7 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  125 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 125 (accept_3_2 4 56 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 125 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  56 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 125 (accept_3_2 1 56 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 125))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 125 (allA_of_3_0 55 55 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 125
  (allA_succ_of_accept 53 54 125 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 125 (accept_3_2 52 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 50
  54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 125 (accept_3_2 49 54
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 125
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 48 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 125 (accept_3_2 46 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 125 (Polychromatic418967fa.accept_13_6_2_8_1_1782 45 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 125 (Polychromatic418967fa.accept_15_14_9_5_1_3932
  44 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 125 (accept_3_2 43
  54 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 125
  (Polychromatic418967fa.accept_15_12_9_5_1_2973 42 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 125 (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 125 (accept_3_2 40 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 125 (Polychromatic418967fa.accept_11_5_10_4_1_1157
  38 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 125 (accept_3_2 37
  54 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 125
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 125 (accept_3_2 34 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 125 (Polychromatic418967fa.accept_13_7_2_8_1_1746 33 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 125 (Polychromatic418967fa.accept_7_4_5_6_1_344 32
  54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 125 (accept_3_2 31 54
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 125
  (Polychromatic418967fa.accept_20_10_14_5_1_3331 30 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 125 (accept_3_2 28 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 125 (Polychromatic418967fa.accept_10_6_4_5_1_615
  26 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 125 (accept_3_2 25
  54 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 125
  (Polychromatic418967fa.accept_19_5_16_11_1_4727 24 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 125 (accept_3_2 22 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 125 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 125 (Polychromatic418967fa.accept_13_7_2_8_1_1746
  20 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 125 (accept_3_2 19
  54 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 125
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 125 (Polychromatic418967fa.accept_22_17_10_15_1_6062 17 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 125 (accept_3_2 16 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 125 (Polychromatic418967fa.accept_15_14_9_5_1_3932
  14 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 125 (accept_3_2 13
  54 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 125
  (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 125 (accept_3_2 10 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 125 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 54 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 54
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 125 (accept_3_2 7 54 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 125 (Polychromatic418967fa.accept_10_6_4_5_1_615 6
  54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 54 125
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 54 125 (accept_3_2 4 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 54
  125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 54 125 (Polychromatic418967fa.accept_19_2_16_11_1_6045 2 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 125 (accept_3_2 1 54 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 54 125)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 125
  (allA_succ_of_accept 52 53 125 (accept_3_2 52 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  53 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 125 (Polychromatic418967fa.accept_13_11_1_8_1_1776 50 53 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 125 (accept_3_2 49 53 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 125 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 53 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 125
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 125 (accept_3_2 46 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 125 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 125 (accept_3_2 43 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 125 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 53 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 125
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 125 (accept_3_2 40 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 125 (Polychromatic418967fa.accept_19_1_15_11_1_4712 39 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 125 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 125 (accept_3_2 37 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 125 (Polychromatic418967fa.accept_27_9_26_17_1_980 36 53 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 125
  (Polychromatic418967fa.accept_11_2_9_4_1_310 35 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 125 (accept_3_2 34 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 125 (Polychromatic418967fa.accept_10_2_3_5_1_996 32 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 125 (accept_3_2 31 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 53 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 125
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 125 (accept_3_2 28 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 125 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 125 (accept_3_2 25 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 125 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 53 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 125
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 125 (accept_3_2 22 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 125 (Polychromatic418967fa.accept_17_4_2_6_1_2629 21 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 125 (Polychromatic418967fa.accept_13_7_1_8_1_1778 20 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 125 (accept_3_2 19 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 125 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 53 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 125
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 125 (accept_3_2 16 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 125 (Polychromatic418967fa.accept_20_15_13_5_1_6061 15 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 125 (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 53 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 125 (accept_3_2 13 53 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 53 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 125
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 125 (accept_3_2 10 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 125 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 125 (accept_3_2 7 53 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 125 (Polychromatic418967fa.accept_13_6_1_8_1_1116 6 53 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 125
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 125 (accept_3_2 4 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  125 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 53 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 53 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 125 (accept_3_2 1 53 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 125))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 125 (allA_of_3_0 52 52
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 125 (allA_succ_of_accept 50 51 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 125 (accept_3_2 49 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 125 (accept_3_2 46 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 51 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 125 (accept_3_2 43 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 125 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 125 (accept_3_2 40 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 125 (accept_3_2 37 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 125 (Polychromatic418967fa.accept_13_9_12_8_1_570 35 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 125 (accept_3_2 34 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 125 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 51 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 125 (accept_3_2 31 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 125 (accept_3_2 28 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 125 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 51 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 125 (accept_3_2 25 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 125 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 125 (accept_3_2 22 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 125 (accept_3_2 19 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 125 (accept_3_2 16 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 125 (accept_3_2 13 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 125 (accept_3_2 10 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 125 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 51 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 125 (accept_3_2 7 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 125 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 51 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 125 (accept_3_2 4 51 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 125 (accept_3_2 1 51 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 125)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 125 (allA_succ_of_accept 49 50 125 (accept_3_2 49 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 50 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 125 (accept_3_2 46 50 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 50 125 5 9 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 50 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 44
  50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 125 (accept_3_2 43 50
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 125
  (Polychromatic418967fa.accept_9_6_5_8_1_598 42 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 125 (Polychromatic418967fa.accept_17_7_16_6_1_3705 41 50 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 125 5 8 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 125
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 125 (accept_3_2 37 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 125 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 50 125 5 7 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 50 125 (accept_3_2 34 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 50 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 50 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 125 (Polychromatic418967fa.accept_12_8_2_5_1_844 32 50 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 125 (accept_3_2 31 50 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 125 5 6 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 29
  50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 125 (accept_3_2 28 50
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 125 (Polychromatic418967fa.accept_4_3_2_1_1_50
  27 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 125
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 50 125 25 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 50 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 50 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 125 (accept_3_2 22 50 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 125 5 4 10 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 125 (accept_3_2 19
  50 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 125
  (Polychromatic418967fa.accept_19_18_12_11_1_3386 18 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 125 (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 50 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 125 (accept_3_2 16 50 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 50 125 5 3 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 50 125 (Polychromatic418967fa.accept_13_1_11_8_1_2562 14 50 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 125 (accept_3_2 13 50 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 12
  50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 125 5 2 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 125 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 50 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 125 (accept_3_2 7 50 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 6
  50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 50 125 5 1 10 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 50 125 (accept_3_2 4 50
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 125 (Polychromatic418967fa.accept_4_3_2_1_1_50
  3 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 125
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 125 (accept_3_2 1 50 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  125)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 125 (allA_of_3_0 49 49 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 125 (allA_succ_of_accept 47 48 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 47
  48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 125 (accept_3_2 46 48
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 125
  (Polychromatic418967fa.accept_18_9_12_17_1_6060 45 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 48 125 (Polychromatic418967fa.accept_21_2_6_20_1_6059 44 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 125 (accept_3_2 43 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 48 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 48 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 41
  48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 125 (accept_3_2 40 48
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 48 125
  (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 48 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 125 (accept_3_2 37 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 48 125 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 48 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 125 (Polychromatic418967fa.accept_14_7_6_13_1_4111
  35 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 125 (accept_3_2 34
  48 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 48 125
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 48 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 125 (accept_3_2 31 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 48 125 (Polychromatic418967fa.accept_13_4_9_8_1_1736 30 48 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 29
  48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 125 (accept_3_2 28 48
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 48 125
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 48 125 (Polychromatic418967fa.accept_14_12_6_13_1_3173 26 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 125 (accept_3_2 25 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 48 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 48 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 23
  48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 125 (accept_3_2 22 48
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 48 125
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 21 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 48 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 125 (accept_3_2 19 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 48 125 (Polychromatic418967fa.accept_19_18_10_11_1_6058 18 48 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 125
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 125 (accept_3_2 16 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 48 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 125 (accept_3_2 13 48 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 125 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 48 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 125
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 125 (accept_3_2 10 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 125 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 125 (Polychromatic418967fa.accept_15_8_3_5_1_608 8 48 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 125 (accept_3_2 7 48 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 48 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 125
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 125 (accept_3_2 4 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  125 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 48 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 125 (accept_3_2 1 48 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 125)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 125 (allA_succ_of_accept 46
  47 125 (accept_3_2 46 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 125
  (Polychromatic418967fa.accept_17_11_13_6_1_2625 45 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 125 (Polychromatic418967fa.accept_15_14_2_5_1_1272 44 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 125 (accept_3_2 43 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 41
  47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 125 (accept_3_2 40 47
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 125
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 125 (accept_3_2 37 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 125
  (Polychromatic418967fa.accept_16_3_15_13_1_2825 35 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 125 (accept_3_2 34 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 125 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 125 (accept_3_2 31 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 125
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 125 (accept_3_2 28 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 125 (Polychromatic418967fa.accept_15_12_2_5_1_3939 27 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 125 (accept_3_2 25 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 47 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 125 (accept_3_2 22 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 125 (Polychromatic418967fa.accept_14_6_5_13_1_367 20 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 125 (accept_3_2 19 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 125
  (Polychromatic418967fa.accept_19_17_9_11_1_6057 17 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 125 (accept_3_2 16 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 125 (accept_3_2 13 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 125
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 125 (accept_3_2 10 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 125 (Polychromatic418967fa.accept_20_9_7_5_1_2114 9 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 125 (accept_3_2 7 47 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 125 (accept_3_2 4 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  125 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 47 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 125 (accept_3_2 1 47 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 125))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 125 (allA_of_3_0 46 46 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 125 (allA_succ_of_accept 44 45 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 125 (accept_3_2 43 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 125 (Polychromatic418967fa.accept_19_4_7_11_1_6056 42 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 125 (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 45 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 125 5 8 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 45 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 39
  45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 125 (accept_3_2 37 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 125 (Polychromatic418967fa.accept_22_14_1_15_1_6055 36 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 45 125 5 7 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 45 125 (accept_3_2 34 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 45 125 (Polychromatic418967fa.accept_18_15_9_17_1_6043 33 45 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 125 (accept_3_2 31 45 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 125 5 6 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 125 (Polychromatic418967fa.accept_17_12_11_6_1_3729
  29 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 125 (accept_3_2 28
  45 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 125
  (Polychromatic418967fa.accept_12_3_9_5_1_853 27 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 125 5 5 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 45 125 (Polychromatic418967fa.accept_13_11_6_8_1_1121 24 45 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 125
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 125 (accept_3_2 22 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  45 125 (Polychromatic418967fa.accept_17_4_11_6_1_3730 21 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 45 125 5 4 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 45 125 (accept_3_2 19 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 45 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 45 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 125 (Polychromatic418967fa.accept_21_17_3_20_1_6054 17 45
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 125 (accept_3_2 16 45 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 125 5 3 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 14
  45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 125 (accept_3_2 13 45
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 125
  (Polychromatic418967fa.accept_17_12_11_6_1_3729 12 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 45 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45 125 5 2 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 45 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 125 (accept_3_2 7 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  125 (Polychromatic418967fa.accept_21_6_3_20_1_6053 6 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 45 125 5 1 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 45 125 (accept_3_2 4 45 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 125 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 45 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 125 (accept_3_2 1 45 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 125))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  125 (allA_succ_of_accept 43 44 125 (accept_3_2 43 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 125 (Polychromatic418967fa.accept_13_3_5_8_1_1099 42 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 125 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 44 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 125 (accept_3_2 40 44 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 125
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 125 (accept_3_2 37 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 125 (Polychromatic418967fa.accept_19_16_6_11_1_6052 35 44 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 125 (accept_3_2 34 44 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 125
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 125 (accept_3_2 31 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 125 (Polychromatic418967fa.accept_20_10_4_5_1_6051 30 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 44 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 125 (accept_3_2 28 44 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 125
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 125 (accept_3_2 25 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 125 (Polychromatic418967fa.accept_13_10_5_8_1_2555 23 44 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 125 (accept_3_2 22 44 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 125
  (Polychromatic418967fa.accept_16_4_12_13_1_990 20 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 125 (accept_3_2 19 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 44 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 125 (accept_3_2 16 44 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 125
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 125 (accept_3_2 13 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 125 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 44 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 125 (accept_3_2 10 44 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 125
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 125 (accept_3_2 7 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  125 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 125 (Polychromatic418967fa.accept_18_5_8_17_1_3478 5 44 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 125 (accept_3_2 4 44 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 125 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  44 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 125 (accept_3_2 1 44 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 125)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  125 (allA_of_3_0 43 43 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 125 (allA_succ_of_accept 41 42 125
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 125 (accept_3_2 40 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 125 (accept_3_2 37 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 125 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 42 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 125 (accept_3_2 34 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 125 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 125 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 125 (accept_3_2 31 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 42 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 125
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 125 (accept_3_2 28 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 125 (Polychromatic418967fa.accept_17_9_8_6_1_6050 26 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 125 (accept_3_2 25 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 125 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 42 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 125 (accept_3_2 22 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 125 (accept_3_2 19 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 125 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 42 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 125
  (Polychromatic418967fa.accept_10_7_2_5_1_298 17 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 125 (accept_3_2 16 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 125 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 125 (accept_3_2 13 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 42 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 125 (accept_3_2 10 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 125 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 42 125 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 125 (accept_3_2 7 42 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 125 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 42 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 125
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 125 (accept_3_2 4 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42
  125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 42 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 125 (accept_3_2 1 42 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 125)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 125 (allA_succ_of_accept 40 41
  125 (accept_3_2 40 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 125
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 125 (accept_3_2 37 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 125 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 41 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 125 (Polychromatic418967fa.accept_20_15_1_5_1_6049
  35 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 125 (accept_3_2 34
  41 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 125
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 125 (Polychromatic418967fa.accept_13_6_2_8_1_1782 32 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 125 (accept_3_2 31 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 41 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 29
  41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 125 (accept_3_2 28 41
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 125
  (Polychromatic418967fa.accept_19_8_3_11_1_6048 27 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 41 125 (Polychromatic418967fa.accept_10_6_1_5_1_1024 26 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 125 (accept_3_2 25 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 41 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 41 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 125 (Polychromatic418967fa.accept_11_1_8_4_1_717
  23 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 125 (accept_3_2 22
  41 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 125
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 125 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 125 (accept_3_2 19 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 125 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 41 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 125 (Polychromatic418967fa.accept_15_2_11_5_1_1266
  17 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 125 (accept_3_2 16
  41 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 125
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 41 125 (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 125 (accept_3_2 13 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 41 125 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 41 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 11
  41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 125 (accept_3_2 10 41
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 125
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 41 125 (Polychromatic418967fa.accept_15_8_11_5_1_169 8 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 125 (accept_3_2 7 41 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 41 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 41 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 125 (Polychromatic418967fa.accept_16_5_9_13_1_3845
  5 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 125 (accept_3_2 4 41
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 125 (Polychromatic418967fa.accept_9_3_5_8_1_99
  3 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 125
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 41 125 (accept_3_2 1 41 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41
  125))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 125 (allA_of_3_0 40 40 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 39 125 (allA_succ_of_accept 38 39 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 125 (accept_3_2 37 39 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 125 (Polychromatic418967fa.accept_10_6_9_5_1_1046
  36 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 125
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 39 125 (accept_3_2 34 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  39 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 39 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 125 (accept_3_2 31 39 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 125
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 125 (accept_3_2 28 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  39 125 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 39 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 125 (accept_3_2 25 39 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 125 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 39 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 125
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 125 (accept_3_2 22 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  39 125 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 39 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 125 (accept_3_2 19 39 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 125
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 39 125 (accept_3_2 16 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  39 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 39 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 125 (accept_3_2 13 39 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 125
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 125 (accept_3_2 10 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  39 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 39 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 125 (accept_3_2 7 39 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 125
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 39 125 (accept_3_2 4 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39
  125 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 39 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 39 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 125 (accept_3_2 1 39 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 39 125))))))))))))))))))))))))))))))))))))))) (allB_succ 38 125 (allA_succ_of_accept 37 38 125
  (accept_3_2 37 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 38 125
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 38 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 125 (accept_3_2 34 38 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 38 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 32
  38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 38 125 (accept_3_2 31 38
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 38 125 (Polychromatic418967fa.accept_7_2_3_6_1_4
  30 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 38 125
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 38 125 (accept_3_2 28 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  38 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 38 125 (Polychromatic418967fa.accept_15_11_8_5_1_1278 26 38 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 38 125 (accept_3_2 25 38 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 38 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 38 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 38 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 38 125 (accept_3_2 22 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  38 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 38 125 (Polychromatic418967fa.accept_12_8_2_5_1_844 20 38 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 38 125 (accept_3_2 19 38 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 38 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 38 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 38 125
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 38 125 (accept_3_2 16 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  38 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 38 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 38 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 38 125 (accept_3_2 13 38 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 38 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 38 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 38 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 38 125 (accept_3_2 10 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  38 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 38 125 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 38 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 38 125 (accept_3_2 7 38 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 38 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 38 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 38 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 38 125 (accept_3_2 4 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 38
  125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 38 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 38 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 125 (accept_3_2 1 38 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 125)))))))))))))))))))))))))))))))))))))) (allB_succ 37 125 (allA_of_3_0 37 37 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 125 (allA_succ_of_accept 35 36 125
  (Polychromatic418967fa.accept_14_7_8_13_1_3161 35 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 125 (accept_3_2 34 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 125 (Polychromatic418967fa.accept_19_13_17_11_1_4716 32 36 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 125 (accept_3_2 31 36 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 36 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 125
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 125 (accept_3_2 28 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 125 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 36 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 125 (accept_3_2 25 36 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 125 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 36 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 125
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 125 (accept_3_2 22 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 125 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 125 (Polychromatic418967fa.accept_13_7_10_8_1_567 20 36 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 125 (accept_3_2 19 36 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 125 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 36 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 125
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 125 (accept_3_2 16 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 125 (Polychromatic418967fa.accept_13_2_10_8_1_1126 15 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 125 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 36 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 125 (accept_3_2 13 36 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 36 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 125
  (Polychromatic418967fa.accept_10_1_6_5_1_304 11 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 125 (accept_3_2 10 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 125 (Polychromatic418967fa.accept_16_8_4_13_1_1014 8 36 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 125 (accept_3_2 7 36 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 125 (Polychromatic418967fa.accept_16_6_4_13_1_3841 6 36 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 125
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 125 (accept_3_2 4 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  125 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3 36 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 36 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 36 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 125 (accept_3_2 1 36 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 36 125)))))))))))))))))))))))))))))))))))) (allB_succ 35 125 (allA_succ_of_accept 34 35
  125 (accept_3_2 34 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 125
  (Polychromatic418967fa.accept_13_7_9_8_1_188 33 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 125 (Polychromatic418967fa.accept_19_13_16_11_1_6047 32 35 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 125 (accept_3_2 31 35 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 35 125 5 6 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 35 125 (Polychromatic418967fa.accept_13_3_9_8_1_4202 29 35 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 125 (accept_3_2 28 35 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 125 (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 35 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 125 5 5 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 125 (Polychromatic418967fa.accept_13_11_9_8_1_1125 24 35 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 125 (Polychromatic418967fa.accept_19_4_16_11_1_6046 23 35
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 125 (accept_3_2 22 35 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 125
  (Polychromatic418967fa.accept_19_2_16_11_1_6045 21 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 35 125 5 4 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 35 125 (accept_3_2 19 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 125 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 35 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 125 (accept_3_2 16 35 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 35 125 5 3 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 35 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 125 (accept_3_2 13 35 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 125 (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 35
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 125
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 35 125 5 2 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 35 125 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 35 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 125 (Polychromatic418967fa.accept_14_8_7_13_1_4113 8 35 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 125 (accept_3_2 7 35 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 125 5 1 7 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 125 (accept_3_2 4 35
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 125
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 35 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 125 (accept_3_2 1 35 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 125))))))))))))))))))))))))))))))))))) (allB_succ 34 125 (allA_of_3_0 34 34 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 33 125 (allA_succ_of_accept 32 33 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 125 (accept_3_2 31 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 33 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 125 (accept_3_2 28 33 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 125 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 33 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 125 (accept_3_2 25 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 125 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 125 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 33 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 125 (accept_3_2 22 33 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 125 (accept_3_2 19 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 125 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 125 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 33 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 125 (accept_3_2 16 33 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 33 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 125 (accept_3_2 13 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 125 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 125 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 33 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 125 (accept_3_2 10 33 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 125 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 33 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 125 (accept_3_2 7 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  125 (Polychromatic418967fa.accept_14_6_5_13_1_367 6 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 33 125 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 33 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 125 (accept_3_2 4 33 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 33 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 125 (accept_3_2 1 33 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33
  125))))))))))))))))))))))))))))))))) (allB_succ 32 125 (allA_succ_of_accept 31 32 125 (accept_3_2 31 32 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 32 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 125
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 32 125 (accept_3_2 28 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  32 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 32 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 32 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 125 (accept_3_2 25 32 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 125 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 32 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 32 125
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 32 125 (accept_3_2 22 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  32 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 32 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 32 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 125 (accept_3_2 19 32 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 125 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 32 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 32 125
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 32 125 (accept_3_2 16 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  32 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 32 125 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 32 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 125 (accept_3_2 13 32 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 32 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 125
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 32 125 (accept_3_2 10 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  32 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 32 125 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 32 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 125 (accept_3_2 7 32 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 125 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 32 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 125
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 125 (accept_3_2 4 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32
  125 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 32 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 125 (accept_3_2 1 32 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 125)))))))))))))))))))))))))))))))) (allB_succ 31 125 (allA_of_3_0 31 31 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 125 (allA_succ_of_accept 29 30 125
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 125 (accept_3_2 28 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 125 (Polychromatic418967fa.accept_16_10_14_13_1_1870 26 30 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 30 125 5 5 6 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 30 125
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 125 (accept_3_2 22 30 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 125 (Polychromatic418967fa.accept_20_1_10_5_1_6044 21 30 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 125 5 4 6 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 125 (accept_3_2 19 30 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 125 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 30 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 125
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 125 (accept_3_2 16 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30
  125 5 3 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  30 125 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 30 125 (accept_3_2 13 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 30 125 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 30 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 125 5 2 6 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 125
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 30 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 125 (accept_3_2 7 30 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 30 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 30 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 30 125 5 1 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 30 125 (accept_3_2 4 30 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 125
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 125 (accept_3_2 1 30 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  125)))))))))))))))))))))))))))))) (allB_succ 29 125 (allA_succ_of_accept 28 29 125 (accept_3_2 28 29 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 125 (Polychromatic418967fa.accept_17_10_12_6_1_4917 27 29
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 125
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 125 (accept_3_2 25 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 29 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 125 (accept_3_2 22 29 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 29 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 125
  (Polychromatic418967fa.accept_13_7_3_8_1_1750 20 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 125 (accept_3_2 19 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 125 (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 125 (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 29 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 125 (accept_3_2 16 29 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 29 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 125
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 125 (accept_3_2 13 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 125 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 29 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 125 (accept_3_2 10 29 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 29 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 125
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 125 (accept_3_2 7 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  125 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 29 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 125 (accept_3_2 4 29 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 29 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  29 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 125 (accept_3_2 1 29 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 125))))))))))))))))))))))))))))) (allB_succ 28 125 (allA_of_3_0
  28 28 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 125 (allA_succ_of_accept 26 27 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 125 (accept_3_2 25 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 125 (Polychromatic418967fa.accept_13_11_1_8_1_1776 24 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 125 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 27 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 125 (accept_3_2 22 27 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 125 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 27 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 125 (accept_3_2 19 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 125 (Polychromatic418967fa.accept_15_2_12_5_1_2107 17 27 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 125 (accept_3_2 16 27 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 125 (Polychromatic418967fa.accept_18_15_9_17_1_6043 15 27
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 125 (accept_3_2 13 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 125 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 125 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 27 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 125 (accept_3_2 10 27 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 125 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 27 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 125 (accept_3_2 7 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 125 (Polychromatic418967fa.accept_13_5_1_8_1_1115 5 27 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 125 (accept_3_2 4 27 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 125 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 27 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 125 (accept_3_2 1 27 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 125))))))))))))))))))))))))))) (allB_succ 26 125
  (allA_succ_of_accept 25 26 125 (accept_3_2 25 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  26 125 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 26 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 125 (accept_3_2 22 26 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 26 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 125
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 26 125 (accept_3_2 19 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  26 125 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 26 125 (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 26 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 125 (accept_3_2 16 26 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 125
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 125 (accept_3_2 13 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  26 125 (Polychromatic418967fa.accept_16_12_10_13_1_1042 12 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 125 (accept_3_2 10 26 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 26 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 125
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 125 (accept_3_2 7 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  125 (Polychromatic418967fa.accept_14_6_12_13_1_3180 6 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 26 125 (Polychromatic418967fa.accept_16_5_10_13_1_6042 5 26 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 125 (accept_3_2 4 26 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 125
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 2 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 125 (accept_3_2 1 26 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  125)))))))))))))))))))))))))) (allB_succ 25 125 (allA_of_3_0 25 25 125 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 125 (allA_succ_of_accept 23 24 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 24 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 125 (accept_3_2 22 24 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 125
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 125 (accept_3_2 19 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  24 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 125 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 24 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 125 (accept_3_2 16 24 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 125 (Polychromatic418967fa.accept_18_15_6_17_1_2386 15 24 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 125
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 125 (accept_3_2 13 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  24 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 24 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 24 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 125 (accept_3_2 10 24 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 125
  (Polychromatic418967fa.accept_22_8_2_15_1_6041 8 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 24 125 (accept_3_2 7 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24
  125 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 24 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 125 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 24 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 125 (accept_3_2 4 24 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 24 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 24
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 125 (accept_3_2 1 24 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 125)))))))))))))))))))))))) (allB_succ 23 125
  (allA_succ_of_accept 22 23 125 (accept_3_2 22 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  23 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 23 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 125 (accept_3_2 19 23 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 125
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 125 (accept_3_2 16 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 125 (accept_3_2 13 23 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 23 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 125
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 125 (accept_3_2 10 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 125 (Polychromatic418967fa.accept_16_9_7_13_1_4997 9 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 125 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 23 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 125 (accept_3_2 7 23 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 125
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 5 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 125 (accept_3_2 4 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  125 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 23 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 125 (accept_3_2 1 23 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 125))))))))))))))))))))))) (allB_succ 22 125 (allA_of_3_0 22 22 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 21 125 (allA_succ_of_accept 20 21 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 125 (accept_3_2 19 21 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 125 (Polychromatic418967fa.accept_15_3_6_5_1_2079
  18 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 125
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 125 (accept_3_2 16 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 21 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 125 (accept_3_2 13 21 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 125 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 21 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 125
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 125 (accept_3_2 10 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 125 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 125 (accept_3_2 7 21 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 21 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 125
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 125 (accept_3_2 4 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  125 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 21 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 125 (accept_3_2 1 21 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 21 125))))))))))))))))))))) (allB_succ 20 125 (allA_succ_of_accept 19 20 125 (accept_3_2 19 20
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 125
  (Polychromatic418967fa.accept_17_1_3_6_1_3672 18 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 125 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 20 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 125 (accept_3_2 16 20 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 20 125 5 3 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 20 125 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 20 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 125 (accept_3_2 13 20 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 125 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 20 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 125
  (Polychromatic418967fa.accept_18_11_2_17_1_3490 11 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 20 125 5 2 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 20 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 125 (Polychromatic418967fa.accept_16_8_4_13_1_1014 8 20 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 125 (accept_3_2 7 20 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 125 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 20 125 5 1 4 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 20 125 (accept_3_2 4 20
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 125 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 125
  (Polychromatic418967fa.accept_11_2_9_4_1_310 2 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 125 (accept_3_2 1 20 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  125)))))))))))))))))))) (allB_succ 19 125 (allA_of_3_0 19 19 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  18 125 (allA_succ_of_accept 17 18 125 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 18 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 125 (accept_3_2 16 18 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 125
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 125 (accept_3_2 13 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 125 (accept_3_2 10 18 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 18 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 125
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 125 (accept_3_2 7 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  125 (Polychromatic418967fa.accept_15_6_3_5_1_607 6 18 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 18 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 125 (accept_3_2 4 18 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  18 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 125 (accept_3_2 1 18 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 125)))))))))))))))))) (allB_succ 17 125 (allA_succ_of_accept 16
  17 125 (accept_3_2 16 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 125
  (Polychromatic418967fa.accept_20_15_17_5_1_6040 15 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 125 (Polychromatic418967fa.accept_15_14_2_5_1_1272 14 17 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 125 (accept_3_2 13 17 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 125 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 17 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 125 (Polychromatic418967fa.accept_7_4_3_6_1_340 11
  17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 125 (accept_3_2 10 17
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 125 (Polychromatic418967fa.accept_7_2_3_6_1_4 9
  17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 125
  (Polychromatic418967fa.accept_10_8_7_5_1_602 8 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 125 (accept_3_2 7 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  125 (Polychromatic418967fa.accept_19_6_17_11_1_6039 6 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 125 (Polychromatic418967fa.accept_16_5_1_13_1_1053 5 17 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 125 (accept_3_2 4 17 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 125 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 17 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 125
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 125 (accept_3_2 1 17 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  125))))))))))))))))) (allB_succ 16 125 (allA_of_3_0 16 16 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15
  125 (allA_succ_of_accept 14 15 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 125 (accept_3_2 13 15 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 11
  15 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 125 5 2 3 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 15 125
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 15 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 125 (accept_3_2 7 15 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 15 125 5 1 3 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 125 (accept_3_2 4 15 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 125 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 15 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 125
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 125 (accept_3_2 1 15 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  125))))))))))))))) (allB_succ 14 125 (allA_succ_of_accept 13 14 125 (accept_3_2 13 14 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 14 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 14 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  14 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 125 (accept_3_2 10 14
  125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 14 125 (Polychromatic418967fa.accept_6_3_2_5_1_32
  9 14 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 125
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 14 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 14 125 (accept_3_2 7 14 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14
  125 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 14 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 14 125 (Polychromatic418967fa.accept_13_5_1_8_1_1115 5 14 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 125 (accept_3_2 4 14 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 14 125 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 125 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 14
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 125 (accept_3_2 1 14 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 125)))))))))))))) (allB_succ 13 125 (allA_of_3_0 13 13 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 125 (allA_succ_of_accept 11 12 125
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 12 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 125 (accept_3_2 10 12 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  12 125 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 12 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 12 125 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 12 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 125 (accept_3_2 7 12 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 125 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 12 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 125
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 12 125 (accept_3_2 4 12 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12
  125 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 12 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 125 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 12 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 125 (accept_3_2 1 12 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 125)))))))))))) (allB_succ 11 125 (allA_succ_of_accept 10 11 125 (accept_3_2 10 11 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 125 (Polychromatic418967fa.accept_7_2_4_6_1_166 9
  11 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 125
  (Polychromatic418967fa.accept_15_8_11_5_1_169 8 11 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 125 (accept_3_2 7 11 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  125 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 125 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 11 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 125 (accept_3_2 4 11 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 125 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 11 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 125 (accept_3_2 1 11 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 125))))))))))) (allB_succ 10 125 (allA_of_3_0 10 10 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 9 125 (allA_succ_of_accept 8 9 125
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 125 (accept_3_2 7 9 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 125
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 9 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 125 (Polychromatic418967fa.accept_16_5_9_13_1_3845 5 9 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 125 (accept_3_2 4 9 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 125 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 9 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 125 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 125 (accept_3_2 1 9 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 125))))))))) (allB_succ 8 125 (allA_succ_of_accept 7 8 125
  (accept_3_2 7 8 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 125
  (Polychromatic418967fa.accept_22_6_8_15_1_6038 6 8 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 125 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 8 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 125 (accept_3_2 4 8 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 125 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 125 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 8
  125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 125 (accept_3_2 1 8 125
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 125)))))))) (allB_succ 7 125 (allA_of_3_0 7 7 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 6 125 (allA_succ_of_accept 5 6 125
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 6 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 125 (accept_3_2 4 6 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 125
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 125 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 6 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 125 (accept_3_2 1 6 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 125)))))) (allB_succ 5 125 (allA_succ_of_accept 4 5 125 (accept_3_2 4 5 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 125 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 5 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 125
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 5 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 125 (accept_3_2 1 5 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 125)))))
  (allB_succ 4 125 (allA_of_3_0 4 4 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 125 (allA_succ_of_accept 2
  3 125 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 125 (accept_3_2 1 3 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 125)))
  (allB_succ 2 125 (allA_succ_of_accept 1 2 125 (accept_3_2 1 2 125 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  125)) (allB_two
  125)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


