-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch112
-- name    : Polychromatic418967fa_Branch112
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:11:04.782741+00:00
-- url     : https://prove2.me/theorems/eb5736e5-78bc-45e9-8be1-b8b5ca51b4e6
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

def Polychromatic418967fa.branch_112 : allB 112 112 :=
  allB_succ' 2 111 112 (Eq.refl Bool.true) (allA_succ_of_accept 1 111 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  111 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111 112)) (allB_succ' 3 110 112
  (Eq.refl Bool.true) (allA_of_3_1 3 110 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 109 112 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 109 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 109 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 112 (accept_3_3 2 109 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 112 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 109 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109 112)))) (allB_succ' 5 108 112 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 108 112 4 1 27 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 108 112 (Polychromatic418967fa.accept_22_3_20_2_1_5223 3 108 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 112 2 1 54 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 112 (Polychromatic418967fa.accept_21_1_3_7_1_3727 1 108 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108 112))))) (allB_succ' 6 107 112 (Eq.refl
  Bool.true) (allA_of_3_1 6 107 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 106 112 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 106 112 2 3 53 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 106 112 (accept_3_3 5 106 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106
  112 2 2 53 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  106 112 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 106 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 106 112 2 1 53 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 106 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 106 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 112))))))) (allB_succ' 8 105 112 (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 105 112 7 1 15 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 105 112 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 105 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 112 (accept_3_3 5 105 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 105 112 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 105 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  105 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 112 (accept_3_3 2 105
  112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 112 (Polychromatic418967fa.accept_6_1_3_4_1_1
  1 105 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105 112)))))))) (allB_succ' 9 104 112
  (Eq.refl Bool.true) (allA_of_3_1 9 104 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 103 112 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 103 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 103 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 112 (accept_3_3 8 103 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 112 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 103 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 112
  (Polychromatic418967fa.accept_11_6_4_2_1_599 6 103 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 112 (accept_3_3 5 103 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 112 (Polychromatic418967fa.accept_13_4_12_8_1_197 4 103 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 112 (accept_3_3 2 103 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 112 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 103 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 112)))))))))) (allB_succ' 11 102 112 (Eq.refl
  Bool.true) (allA_succ_of_gcd 10 102 112 2 5 51 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 102 112 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 102 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 112 2 4 51 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 7
  102 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 112 2 3 51 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 112 (accept_3_3 5
  102 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 112 2 2 51 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 102 112
  (Polychromatic418967fa.accept_12_3_6_4_1_400 3 102 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 102 112 2 1 51 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 102 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 102 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 102 112))))))))))) (allB_succ' 12 101 112 (Eq.refl Bool.true) (allA_of_3_1
  12 101 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 100 112 (Eq.refl Bool.true) (allA_succ_of_gcd 12
  100 112 4 3 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 100 112 (accept_3_3 11 100 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 112 2 5 50 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 112
  (Polychromatic418967fa.accept_21_9_16_7_1_5222 9 100 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 100 112 4 2 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 100 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 100 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 112 2 3 50 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 100 112 (accept_3_3 5 100 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 100 112 4 1 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 100 112 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 100 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 112 2 1 50 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 112 (Polychromatic418967fa.accept_13_1_9_8_1_1734 1
  100 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 112))))))))))))) (allB_succ' 14 99
  112 (Eq.refl Bool.true) (allA_succ_of_accept 13 99 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 99 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 112
  (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 99 112 (accept_3_3 11 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  99 112 (Polychromatic418967fa.accept_19_10_4_17_1_1544 10 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 99 112 (Polychromatic418967fa.accept_20_9_19_12_1_5221 9 99 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 112 (accept_3_3 8 99 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 112
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 112 (accept_3_3 5 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99
  112 (Polychromatic418967fa.accept_23_4_7_20_1_5220 4 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 112 (Polychromatic418967fa.accept_21_3_15_7_1_5155 3 99 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 112 (accept_3_3 2 99 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 99 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 112)))))))))))))) (allB_succ' 15 98 112 (Eq.refl
  Bool.true) (allA_of_3_1 15 98 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 97 112 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 97 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 97 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 112 (accept_3_3 14 97 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 97 112 (Polychromatic418967fa.accept_18_13_7_4_1_2738 13 97 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 112
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 112 (accept_3_3 11 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 112 (accept_3_3 8 97 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 112 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 97 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 112
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 112 (accept_3_3 5 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  112 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 97 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 112 (accept_3_3 2 97 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 97 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 112)))))))))))))))) (allB_succ' 17 96 112 (Eq.refl Bool.true)
  (allA_succ_of_gcd 16 96 112 16 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 96 112 (Polychromatic418967fa.accept_18_15_6_4_1_5147 15 96 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 112 2 7 48 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 112 (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 96 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 112 4 3 24 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 112 (accept_3_3 11 96 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 112 2 5 48 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 112 (Polychromatic418967fa.accept_19_9_1_17_1_3879 9
  96 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 112 8 1 12 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 112
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 112 2 3 48 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 112 (accept_3_3 5 96 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 112
  4 1 24 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96
  112 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 96 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 96 112 2 1 48 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 96 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96 112))))))))))))))))) (allB_succ' 18 95 112 (Eq.refl Bool.true)
  (allA_of_3_1 18 95 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 94 112 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 94 112 2 9 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 112 (accept_3_3 17 94 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94
  112 2 8 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  94 112 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 94 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 94 112 2 7 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 94 112 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 94 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 112 2 6 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 112 (accept_3_3 11 94 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 112 2 5 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 94 112 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 94 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 94 112 2 4 47 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 94 112
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 94 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 94 112 2 3 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 94 112 (accept_3_3 5 94 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 112
  2 2 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 94
  112 (Polychromatic418967fa.accept_15_3_4_7_1_1352 3 94 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 94 112 2 1 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 94 112 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 94 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 112))))))))))))))))))) (allB_succ' 20 93 112 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 93 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 93 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 112 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 93 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 112 (accept_3_3 17 93 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 16
  93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 112
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 112 (accept_3_3 14 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 112 (Polychromatic418967fa.accept_15_12_3_7_1_4123 12 93 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 112 (accept_3_3 11 93 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 93 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 112
  (Polychromatic418967fa.accept_25_9_18_12_1_5219 9 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 112 (accept_3_3 8 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  112 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 93 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 112 (accept_3_3 5 93 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 112 (Polychromatic418967fa.accept_15_4_3_7_1_713 4 93 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 112 (Polychromatic418967fa.accept_20_3_13_12_1_5218
  3 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 112 (accept_3_3 2 93
  112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 112)))))))))))))))))))) (allB_succ'
  21 92 112 (Eq.refl Bool.true) (allA_of_3_1 21 92 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 91 112
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 91 112 7 3 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 91 112 (accept_3_3 20 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 91 112 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 91 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 112 (Polychromatic418967fa.accept_24_18_19_16_1_5217 18 91
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 112 (accept_3_3 17 91 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 16
  91 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 91 112 7 2 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 91 112 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 91 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 112 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 91 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 112 (accept_3_3 11 91 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 112 (Polychromatic418967fa.accept_12_10_7_4_1_820
  10 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 112 (accept_3_3 8 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 91 112
  7 1 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 91
  112 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 112 (accept_3_3 5 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  112 (Polychromatic418967fa.accept_17_4_6_10_1_5164 4 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 112 (accept_3_3 2 91 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 112 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 91 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 112)))))))))))))))))))))) (allB_succ' 23 90 112
  (Eq.refl Bool.true) (allA_succ_of_gcd 22 90 112 2 11 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 90 112 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 90 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 112 2 10 45 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 112
  (Polychromatic418967fa.accept_24_19_18_16_1_5216 19 90 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 90 112 2 9 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 90 112 (accept_3_3 17 90 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 90 112 2 8 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 90 112 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 90 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 112 2 7 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 112 (Polychromatic418967fa.accept_17_13_5_10_1_2839 13 90
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 112 2 6 45 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 112 (accept_3_3 11
  90 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 112 2 5 45 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 112
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 90 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 112 2 4 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 112 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 90 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 112 2 3 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 112 (accept_3_3 5 90 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 90 112 2 2 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 90 112 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 90 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 112 2 1 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 112 (Polychromatic418967fa.accept_13_1_12_8_1_1818 1
  90 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90 112)))))))))))))))))))))))
  (allB_succ' 24 89 112 (Eq.refl Bool.true) (allA_of_3_1 24 89 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  25 88 112 (Eq.refl Bool.true) (allA_succ_of_gcd 24 88 112 8 3 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 112 (accept_3_3 23 88 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 88 112 2 11 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 88 112 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 88 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 88 112 4 5 22 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 112
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 88 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 88 112 2 9 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 112 (accept_3_3 17 88 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  112 8 2 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 112 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 88 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 112 2 7 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 88 112 (Polychromatic418967fa.accept_17_13_3_10_1_5157 13 88 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 112 4 3 22 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 112 (accept_3_3 11 88 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 112 2 5 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 88 112 (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 88 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 112 8 1 11 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 112
  (Polychromatic418967fa.accept_13_7_10_8_1_567 7 88 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 88 112 2 3 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 88 112 (accept_3_3 5 88 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 112
  4 1 22 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88
  112 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 88 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 88 112 2 1 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 88 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 88 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 88 112))))))))))))))))))))))))) (allB_succ' 26 87 112 (Eq.refl Bool.true)
  (allA_succ_of_accept 25 87 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 87 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 112 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 87 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 112 (accept_3_3 23 87 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 112 (Polychromatic418967fa.accept_20_2_7_12_1_5215
  22 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 112
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 112 (accept_3_3 20 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 112 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 87 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 112 (accept_3_3 17 87 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 112 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 87 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 112
  (Polychromatic418967fa.accept_10_5_7_2_1_516 15 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 112 (accept_3_3 14 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 87 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 112 (accept_3_3 11 87 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 87 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 112
  (Polychromatic418967fa.accept_10_9_7_2_1_887 9 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 112 (accept_3_3 8 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  112 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 112 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 87 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 112 (accept_3_3 5 87 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 112 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 87 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 112 (accept_3_3 2 87 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 87
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 112))))))))))))))))))))))))))
  (allB_succ' 27 86 112 (Eq.refl Bool.true) (allA_of_3_1 27 86 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  28 85 112 (Eq.refl Bool.true) (allA_succ_of_accept 27 85 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 85 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 112 (accept_3_3 26 85 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 112 (Polychromatic418967fa.accept_13_12_7_8_1_1104
  25 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 112
  (Polychromatic418967fa.accept_21_3_1_7_1_5187 24 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 112 (accept_3_3 23 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 112 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 112 (accept_3_3 20 85 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 112 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 85 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 112
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 112 (accept_3_3 17 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 112 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 85 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 112 (accept_3_3 14 85 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 112 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 85 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 112
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 112 (accept_3_3 11 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 112 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 112 (accept_3_3 8 85 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 112 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 85 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 112
  (Polychromatic418967fa.accept_19_6_9_17_1_5214 6 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 112 (accept_3_3 5 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  112 (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 85 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 85 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 112 (accept_3_3 2 85 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 112 (Polychromatic418967fa.accept_13_1_7_8_1_1796 1 85 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 112)))))))))))))))))))))))))))) (allB_succ' 29 84 112
  (Eq.refl Bool.true) (allA_succ_of_gcd 28 84 112 28 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 84 112 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 84 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 112 2 13 42 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 112
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 84 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 112 4 6 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 112 (accept_3_3 23 84 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84
  112 2 11 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 84
  112 7 3 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 84
  112 4 5 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19
  84 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 84 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 84 112 2 9 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 84 112 (accept_3_3 17 84 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 84 112 4 4 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 84 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 84 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 112 14 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 112 (Polychromatic418967fa.accept_15_13_9_7_1_2194 13 84 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 112 4 3 21 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 112 (accept_3_3 11 84 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 112 2 5 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 112 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9
  84 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 112 4 2 21 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 84 112 7 1 12 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 84 112 2 3 42 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 112 (accept_3_3 5 84
  112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 112 4 1 21 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 112
  (Polychromatic418967fa.accept_19_3_8_17_1_5213 3 84 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 84 112 2 1 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 84 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84 112))))))))))))))))))))))))))))) (allB_succ' 30 83 112 (Eq.refl
  Bool.true) (allA_of_3_1 30 83 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 82 112 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 82 112 2 15 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 82 112 (accept_3_3 29 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82
  112 2 14 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  82 112 (Polychromatic418967fa.accept_19_8_6_17_1_5186 27 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 82 112 2 13 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 82 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 82 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 112 2 12 41 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 112 (accept_3_3 23 82 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 112 2 11 41 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 112
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 82 112 2 10 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 82 112 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 82 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 112 2 9 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 112 (accept_3_3 17 82 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 82 112 2 8 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 82 112 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 82 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 112 2 7 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 112 (Polychromatic418967fa.accept_12_1_10_4_1_380
  13 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 112 2 6 41 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 112 (accept_3_3 11
  82 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 112 2 5 41 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 112
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 112 2 4 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 82 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 112 2 3 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 112 (accept_3_3 5 82 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 112 2 2 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 112 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 82 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 112 2 1 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 112 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  82 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 112)))))))))))))))))))))))))))))))
  (allB_succ' 32 81 112 (Eq.refl Bool.true) (allA_succ_of_accept 31 81 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 112
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 81 112 (accept_3_3 29 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  81 112 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 81 112 (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 81 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 112 (accept_3_3 26 81 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 112
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 24 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 81 112 (accept_3_3 23 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  81 112 (Polychromatic418967fa.accept_13_9_3_8_1_573 22 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 81 112 (Polychromatic418967fa.accept_19_2_5_17_1_3850 21 81 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 112 (accept_3_3 20 81 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 81 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 112
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 81 112 (accept_3_3 17 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  81 112 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 81 112 (Polychromatic418967fa.accept_18_15_9_4_1_5185 15 81 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 112 (accept_3_3 14 81 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 112
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 81 112 (accept_3_3 11 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  81 112 (Polychromatic418967fa.accept_21_10_18_7_1_5212 10 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 81 112 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 81 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 112 (accept_3_3 8 81 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 81 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 112
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 112 (accept_3_3 5 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81
  112 (Polychromatic418967fa.accept_21_4_18_7_1_5211 4 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 112 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 81 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 112 (accept_3_3 2 81 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 112)))))))))))))))))))))))))))))))) (allB_succ' 33 80
  112 (Eq.refl Bool.true) (allA_of_3_1 33 80 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 79 112 (Eq.refl
  Bool.true) (allA_succ_of_accept 33 79 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 112 (accept_3_3 32 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 112 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 79 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 112
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 112 (accept_3_3 29 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 112 (accept_3_3 26 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 112 (Polychromatic418967fa.accept_13_12_1_8_1_1779 25 79 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 112
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 112 (accept_3_3 23 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 112 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 112 (accept_3_3 20 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 79 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 112
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 112 (accept_3_3 17 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 112 (Polychromatic418967fa.accept_18_16_7_4_1_3901 16 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 112 (accept_3_3 14 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 112 (Polychromatic418967fa.accept_18_13_7_4_1_2738 13 79 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 112
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 112 (accept_3_3 11 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 112 (accept_3_3 8 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 112 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 79 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 112
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 112 (accept_3_3 5 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  112 (Polychromatic418967fa.accept_17_4_11_10_1_5167 4 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 79 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 112 (accept_3_3 2 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 79 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 112)))))))))))))))))))))))))))))))))) (allB_succ' 35
  78 112 (Eq.refl Bool.true) (allA_succ_of_gcd 34 78 112 2 17 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 112 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 78 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 112 2 16 39 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 112
  (Polychromatic418967fa.accept_19_12_2_17_1_5210 31 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 112 2 15 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 112 (accept_3_3 29 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78
  112 2 14 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  78 112 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 78 112 2 13 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 78 112 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 78 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 112 2 12 39 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 112 (accept_3_3 23 78 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 112 2 11 39 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 112
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 112 2 10 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 78 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 78 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 112 2 9 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 112 (accept_3_3 17 78 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 78 112 2 8 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 78 112 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 78 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 112 2 7 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 112 (Polychromatic418967fa.accept_21_13_15_7_1_5209
  13 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 112 2 6 39 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 112 (accept_3_3 11
  78 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 112 2 5 39 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 112
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 112 2 4 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 112 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 78 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 112 2 3 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 112 (accept_3_3 5 78 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 78 112 2 2 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 78 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 78 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 112 2 1 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 78
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 112)))))))))))))))))))))))))))))))))))
  (allB_succ' 36 77 112 (Eq.refl Bool.true) (allA_of_3_1 36 77 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  37 76 112 (Eq.refl Bool.true) (allA_succ_of_gcd 36 76 112 4 9 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 112 (accept_3_3 35 76 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 76 112 2 17 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 76 112 (Polychromatic418967fa.accept_23_10_7_20_1_5208 33 76 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 112 4 8 19 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 112
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 112 2 15 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 112 (accept_3_3 29 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  112 4 7 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 112 (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 112 2 13 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 112 (Polychromatic418967fa.accept_15_10_1_7_1_5207 25 76 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 112 4 6 19 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 112 (accept_3_3 23 76 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 112 2 11 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 112 (Polychromatic418967fa.accept_10_1_6_2_1_867 21
  76 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 112 4 5 19 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 112
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 19 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 112 2 9 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 112 (accept_3_3 17 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  112 4 4 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 112 (Polychromatic418967fa.accept_17_15_8_10_1_2886 15 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 112 2 7 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 76 112 (Polychromatic418967fa.accept_22_13_10_2_1_5206 13 76 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 112 4 3 19 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 112 (accept_3_3 11 76 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 112 2 5 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 112 (Polychromatic418967fa.accept_13_9_11_8_1_195 9 76 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 112 4 2 19 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 112
  (Polychromatic418967fa.accept_27_7_22_4_1_5205 7 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 76 112 2 3 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 76 112 (accept_3_3 5 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 112
  4 1 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76
  112 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 76 112 2 1 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 76 112 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 76 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 112))))))))))))))))))))))))))))))))))))) (allB_succ' 38 75 112
  (Eq.refl Bool.true) (allA_succ_of_accept 37 75 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 75 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 112
  (Polychromatic418967fa.accept_21_15_12_7_1_5204 36 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 112 (accept_3_3 35 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 75 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 112 (accept_3_3 32 75 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 75 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 112
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 112 (accept_3_3 29 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 112 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 75 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 112 (accept_3_3 26 75 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 75 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 112
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 112 (accept_3_3 23 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 112 (Polychromatic418967fa.accept_21_1_12_7_1_3783 22 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 112 (Polychromatic418967fa.accept_26_21_23_8_1_5203 21 75 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 112 (accept_3_3 20 75 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 112
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 112 (accept_3_3 17 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 75 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 112 (accept_3_3 14 75 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 75 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 112
  (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 112 (accept_3_3 11 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 112 (Polychromatic418967fa.accept_23_9_6_20_1_5202 9 75 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 112 (accept_3_3 8 75 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 112
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 112 (accept_3_3 5 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  112 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 112 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 75 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 112 (accept_3_3 2 75 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 75 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 112)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 74 112
  (Eq.refl Bool.true) (allA_of_3_1 39 74 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 73 112 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 73 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 112 (accept_3_3 38 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 112 (Polychromatic418967fa.accept_19_18_16_17_1_2626 37 73 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 112
  (Polychromatic418967fa.accept_15_6_13_7_1_222 36 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 112 (accept_3_3 35 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 112 (accept_3_3 32 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 112 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 73 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 112
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 112 (accept_3_3 29 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 112 (Polychromatic418967fa.accept_25_3_23_12_1_5201 28 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 112 (accept_3_3 26 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 73 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 112
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 112 (accept_3_3 23 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 112 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 112 (accept_3_3 20 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 112 (Polychromatic418967fa.accept_20_19_13_12_1_2476 19 73 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 112
  (Polychromatic418967fa.accept_19_18_16_17_1_2626 18 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 73 112 (accept_3_3 17 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 73 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 73 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 73 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 112 (accept_3_3 14 73 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 112
  (Polychromatic418967fa.accept_17_13_5_10_1_2839 13 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 73 112 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 73 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 112 (accept_3_3 11 73 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 73 112 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 112 (accept_3_3 8 73 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 7
  73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 112
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 112 (accept_3_3 5 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  112 (Polychromatic418967fa.accept_29_4_15_25_1_5200 4 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 112 (accept_3_3 2 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 112 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 73 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 112))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 72 112 (Eq.refl Bool.true) (allA_succ_of_gcd 40 72 112 8 5 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 72 112 (Polychromatic418967fa.accept_19_1_15_17_1_701
  39 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 112 2 19 36 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 112
  (Polychromatic418967fa.accept_11_4_6_2_1_51 37 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 112 4 9 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 112 (accept_3_3 35 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72
  112 2 17 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  72 112 (Polychromatic418967fa.accept_15_3_12_7_1_1346 33 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 72 112 8 4 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 72 112 (Polychromatic418967fa.accept_19_12_15_17_1_3837 31 72 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 112 2 15 36 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 112 (accept_3_3 29 72 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 112 4 7 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 112 (Polychromatic418967fa.accept_13_1_7_8_1_1796
  27 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 112 2 13 36 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 112
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 25 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 112 8 3 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 112 (accept_3_3 23 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72
  112 2 11 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  72 112 (Polychromatic418967fa.accept_15_6_12_7_1_1360 21 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 72 112 4 5 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 72 112 (Polychromatic418967fa.accept_15_4_12_7_1_3115 19 72 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 112 2 9 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 112 (accept_3_3 17 72 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 112 8 2 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 72 112 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 72 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 112 2 7 36 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 112
  (Polychromatic418967fa.accept_19_13_15_17_1_5199 13 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 72 112 4 3 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 72 112 (accept_3_3 11 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 72 112 2 5 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 72 112 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 72 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 112 8 1 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 112 (Polychromatic418967fa.accept_19_7_15_17_1_5198 7 72 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 112 2 3 36 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 112 (accept_3_3 5 72 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 112 4 1 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72 112 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3
  72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 112 2 1 36 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 112
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 1 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 112))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 71 112 (Eq.refl Bool.true) (allA_of_3_1 42 71
  112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 70 112 (Eq.refl Bool.true) (allA_succ_of_gcd 42 70 112 14
  3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 112
  (accept_3_3 41 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 112 2 20 35 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 70 112
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 70 112 2 19 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 70 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 70 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 112 2 18 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 70 112 7 5 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 70 112 2 17 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 112 (Polychromatic418967fa.accept_9_6_7_4_1_212 33
  70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 112 2 16 35 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 112
  (Polychromatic418967fa.accept_11_9_4_2_1_600 31 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 70 112 2 15 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 70 112 (accept_3_3 29 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70
  112 14 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  70 112 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 70 112 2 13 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 70 112 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 70 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 112 2 12 35 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 112 (accept_3_3 23 70 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 112 2 11 35 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 70 112 7 3 10 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 70 112 2 10 35 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 112
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 70 112 2 9 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 70 112 (accept_3_3 17 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70
  112 2 8 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  70 112 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 70 112 14 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 70 112 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 70 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 112 2 6 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 112 (accept_3_3 11 70 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 112 2 5 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 70 112 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 70 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 112 2 4 35 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 70 112 7 1 10 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 70 112 2 3 35 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 112 (accept_3_3 5 70 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 112 2 2 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70 112 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 70 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 112 2 1 35 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 112
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 112))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 69 112 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 69 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 112 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 69 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 112 (accept_3_3 41 69 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 112
  (Polychromatic418967fa.accept_19_2_12_17_1_5197 40 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 69 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 112 (accept_3_3 38 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 69 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 112 (Polychromatic418967fa.accept_13_10_4_8_1_2570
  36 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 112 (accept_3_3 35
  69 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 112
  (Polychromatic418967fa.accept_9_7_6_4_1_483 34 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 69 112 (Polychromatic418967fa.accept_19_14_12_17_1_5196 33 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 112 (accept_3_3 32 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 69 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 69 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 30
  69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 112 (accept_3_3 29 69
  112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 112 (Polychromatic418967fa.accept_9_1_6_4_1_49
  28 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 112
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 112 (accept_3_3 26 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 112 (Polychromatic418967fa.accept_13_11_4_8_1_1098 24 69 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 112 (accept_3_3 23 69 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 112 (Polychromatic418967fa.accept_13_9_4_8_1_1752 22 69 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 112
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 112 (accept_3_3 20 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 112 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 69 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 112 (accept_3_3 17 69 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 112 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 69 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 112
  (Polychromatic418967fa.accept_19_15_12_17_1_5195 15 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 112 (accept_3_3 14 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 69 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 112 (accept_3_3 11 69 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 10
  69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 112
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 112 (accept_3_3 8 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  112 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 112 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 112 (accept_3_3 5 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 112 (Polychromatic418967fa.accept_21_4_6_7_1_3693 4 69 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 112 (accept_3_3 2 69 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  112)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 68 112 (Eq.refl Bool.true) (allA_of_3_1 45 68 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 67 112 (Eq.refl Bool.true) (allA_succ_of_accept 45 67 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 67 112 (accept_3_3 44 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  67 112 (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 67 112 (Polychromatic418967fa.accept_19_4_10_17_1_5194 42 67 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 67 112 (accept_3_3 41 67 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 67 112 (Polychromatic418967fa.accept_17_6_16_10_1_2890 40 67
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 67 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 67 112 (accept_3_3 38 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  67 112 (Polychromatic418967fa.accept_19_18_10_17_1_5192 37 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 67 112 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 67 112 (accept_3_3 35 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 67 112 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 67 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 67 112 (accept_3_3 32 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  67 112 (Polychromatic418967fa.accept_19_12_10_17_1_5189 31 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 67 112 (Polychromatic418967fa.accept_25_5_17_12_1_5193 30 67 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 112 (accept_3_3 29 67 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 67 112 (Polychromatic418967fa.accept_18_10_13_4_1_5153 28 67
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 67 112 (accept_3_3 26 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  67 112 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 67 112 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 112 (accept_3_3 23 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 112 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 67 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 112 (accept_3_3 20 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  67 112 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 67 112 (Polychromatic418967fa.accept_19_18_10_17_1_5192 18 67 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 112 (accept_3_3 17 67 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 112 (Polychromatic418967fa.accept_21_16_4_7_1_5191 16 67
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 112 (accept_3_3 14 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  67 112 (Polychromatic418967fa.accept_21_13_4_7_1_5190 13 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 67 112 (Polychromatic418967fa.accept_19_12_10_17_1_5189 12 67 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 112 (accept_3_3 11 67 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 112 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 67
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 112 (accept_3_3 8 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67
  112 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 67 112 (Polychromatic418967fa.accept_13_6_2_8_1_1782 6 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 112 (accept_3_3 5 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 112 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 67 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 67 112 (accept_3_3 2 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67
  112 (Polychromatic418967fa.accept_19_1_10_17_1_5188 1 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 67 112)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 66 112 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 66 112 2 23 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 66 112 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 66 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 112 2 22 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 43
  66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 112 2 21 33 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 112 (accept_3_3 41
  66 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 112 2 20 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 112
  (Polychromatic418967fa.accept_12_3_6_4_1_400 39 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 112 2 19 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 66 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 66 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 112 2 18 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 112 (accept_3_3 35 66 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 112 2 17 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 66 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 112 2 16 33 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 112
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 112 2 15 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 112 (accept_3_3 29 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66
  112 2 14 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  66 112 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 66 112 2 13 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 66 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 66 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 112 2 12 33 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 112 (accept_3_3 23 66 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 112 2 11 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 112
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 112 2 10 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 66 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 112 2 9 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 112 (accept_3_3 17 66 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 66 112 2 8 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 66 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 66 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 112 2 7 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 112 (Polychromatic418967fa.accept_15_13_6_7_1_1369
  13 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 112 2 6 33 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 112 (accept_3_3 11
  66 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 112 2 5 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 112
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 112 2 4 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 66 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 112 2 3 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 112 (accept_3_3 5 66 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 66 112 2 2 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 66 112 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 66 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 112 2 1 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 66
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  112))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 65 112 (Eq.refl Bool.true) (allA_of_3_1 48 65 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 64 112 (Eq.refl Bool.true) (allA_succ_of_gcd 48 64 112 16 3 4
  7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 64 112
  (accept_3_3 47 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64 112 2 23 32 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 64 112
  (Polychromatic418967fa.accept_21_3_1_7_1_5187 45 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 64 112 4 11 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 64 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 64 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 112 2 21 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 112 (accept_3_3 41 64 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 112 8 5 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 64 112 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 64 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 112 2 19 32 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 112
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 112 4 9 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 64 112 (accept_3_3 35 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64
  112 2 17 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  64 112 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 64 112 16 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 64 112 (Polychromatic418967fa.accept_13_5_12_8_1_198 31 64 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 112 2 15 32 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 112 (accept_3_3 29 64 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 112 4 7 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 112 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 64 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 112 2 13 32 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 112
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 112 8 3 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 64 112 (accept_3_3 23 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64
  112 2 11 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  64 112 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 64 112 4 5 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 64 112 (Polychromatic418967fa.accept_21_19_1_7_1_3724 19 64 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 112 2 9 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 112 (accept_3_3 17 64 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 112 16 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 64 112 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 64 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 112 2 7 32 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 112
  (Polychromatic418967fa.accept_18_13_10_4_1_5150 13 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 64 112 4 3 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 64 112 (accept_3_3 11 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64
  112 2 5 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  64 112 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 64 112 8 1 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 64 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 112 2 3 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 112 (accept_3_3 5 64 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 112 4 1 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 64 112 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 64 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 112 2 1 32 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 112
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 1 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 112))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 63 112 (Eq.refl Bool.true)
  (allA_succ_of_gcd 49 63 112 7 7 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 63 112 (Polychromatic418967fa.accept_13_9_11_8_1_195 48 63 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 112 (accept_3_3 47 63 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 63 112 (Polychromatic418967fa.accept_19_8_6_17_1_5186 46 63 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 112
  (Polychromatic418967fa.accept_10_5_3_2_1_899 45 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 112 (accept_3_3 44 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 63 112 7 6 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 63 112 (accept_3_3 41 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 112 (Polychromatic418967fa.accept_13_1_11_8_1_2562 40 63 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 112 (Polychromatic418967fa.accept_17_5_12_10_1_3963 39 63
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 112 (accept_3_3 38 63 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 37
  63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 112
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 63 112 7 5 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 63 112 (Polychromatic418967fa.accept_15_4_3_7_1_713 34 63 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 112 (Polychromatic418967fa.accept_18_15_9_4_1_5185 33 63
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 112 (accept_3_3 32 63 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 112
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 63 112 (accept_3_3 29 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63
  112 7 4 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  63 112 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 63 112 (accept_3_3 26 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 63 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 112 (Polychromatic418967fa.accept_25_24_13_12_1_3395 24 63
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 112 (accept_3_3 23 63 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 112 (Polychromatic418967fa.accept_13_9_11_8_1_195
  22 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 112 7 3 9 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 112 (accept_3_3 20
  63 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 112
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 63 112 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 63 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 112 (accept_3_3 17 63 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 63 112 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 63 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 112 (Polychromatic418967fa.accept_10_5_3_2_1_899
  15 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 63 112 7 2 9 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 63 112
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 63 112 (Polychromatic418967fa.accept_15_12_3_7_1_4123 12 63 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 112 (accept_3_3 11 63 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 63 112 (Polychromatic418967fa.accept_13_10_11_8_1_1770 10 63 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 112
  (Polychromatic418967fa.accept_13_9_11_8_1_195 9 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 112 (accept_3_3 8 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 63 112
  7 1 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 63 112
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 112 (accept_3_3 5 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  112 (Polychromatic418967fa.accept_13_4_11_8_1_1768 4 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 112 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 63 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 112 (accept_3_3 2 63 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 63 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 112))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 62 112 (Eq.refl Bool.true) (allA_of_3_1 51 62 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  52 61 112 (Eq.refl Bool.true) (allA_succ_of_accept 51 61 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 61 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 112 (accept_3_3 50 61 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 112 (Polychromatic418967fa.accept_10_9_1_2_1_522
  49 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 112
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 112 (accept_3_3 47 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 112 (accept_3_3 44 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 112 (Polychromatic418967fa.accept_10_3_1_2_1_521 43 61 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 112
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 112 (accept_3_3 41 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 112 (Polychromatic418967fa.accept_13_1_9_8_1_1734 40 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 112 (accept_3_3 38 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 61 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 112
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 112 (accept_3_3 35 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 112 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 112 (accept_3_3 32 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 112 (Polychromatic418967fa.accept_18_13_7_4_1_2738 31 61 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 112
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 112 (accept_3_3 29 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 112 (accept_3_3 26 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 112 (Polychromatic418967fa.accept_13_12_9_8_1_2595 25 61 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 112
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 112 (accept_3_3 23 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 112 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 112 (accept_3_3 20 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 61 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 112
  (Polychromatic418967fa.accept_19_18_4_17_1_2618 18 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 112 (accept_3_3 17 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 112 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 112 (accept_3_3 14 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 112 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 61 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 112
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 112 (accept_3_3 11 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 112 (accept_3_3 8 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 112 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 61 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 112
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 112 (accept_3_3 5 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  112 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 61 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 112 (accept_3_3 2 61 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 112))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 60 112 (Eq.refl Bool.true) (allA_succ_of_gcd 52 60 112 4 13 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 112
  (Polychromatic418967fa.accept_18_15_6_4_1_5147 51 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 112 2 25 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 112 (Polychromatic418967fa.accept_24_1_12_16_1_5184 49 60 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 112 4 12 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 112 (accept_3_3 47 60 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 112 2 23 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 112 (Polychromatic418967fa.accept_27_18_6_4_1_5183 45 60 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 112 4 11 15 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 112
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 112 2 21 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 112 (accept_3_3 41 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60
  112 4 10 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  60 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 60 112 2 19 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 60 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 60 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 112 4 9 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 112 (accept_3_3 35 60 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 112 2 17 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 112 (Polychromatic418967fa.accept_17_16_9_10_1_3962
  33 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 112 4 8 15 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 112
  (Polychromatic418967fa.accept_19_12_3_17_1_5182 31 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 112 2 15 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 112 (accept_3_3 29 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60
  112 4 7 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  60 112 (Polychromatic418967fa.accept_19_8_3_17_1_5181 27 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 60 112 2 13 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 60 112 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 60 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 112 4 6 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 112 (accept_3_3 23 60 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 112 2 11 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 21
  60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 112 4 5 15 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 112
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 112 2 9 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 112 (accept_3_3 17 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60
  112 4 4 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  60 112 (Polychromatic418967fa.accept_18_15_6_4_1_5147 15 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 60 112 2 7 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 60 112 (Polychromatic418967fa.accept_17_13_9_10_1_2888 13 60 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 112 4 3 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 112 (accept_3_3 11 60 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 112 2 5 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 112 (Polychromatic418967fa.accept_21_9_18_7_1_5180 9 60 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 112 4 2 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 112
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 112 2 3 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 112 (accept_3_3 5 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 112
  4 1 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60
  112 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 112 2 1 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 60 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 112))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54
  59 112 (Eq.refl Bool.true) (allA_of_3_1 54 59 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 58 112
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 58 112 2 27 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 58 112 (accept_3_3 53 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 58 112 2 26 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 58 112 (Polychromatic418967fa.accept_15_6_13_7_1_222 51 58 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 112 2 25 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 112 (Polychromatic418967fa.accept_12_1_10_4_1_380
  49 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 58 112 2 24 29 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 58 112 (accept_3_3 47
  58 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58 112 2 23 29 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 58 112
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 58 112 2 22 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 58 112 (Polychromatic418967fa.accept_12_7_10_4_1_382 43 58 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 112 2 21 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 112 (accept_3_3 41 58 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 112 2 20 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 112 (Polychromatic418967fa.accept_15_9_13_7_1_1361 39 58 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 58 112 2 19 29 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 58 112
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 58 112 2 18 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 58 112 (accept_3_3 35 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58
  112 2 17 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  58 112 (Polychromatic418967fa.accept_17_16_7_10_1_5179 33 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 58 112 2 16 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 58 112 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 58 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 58 112 2 15 29 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 58 112 (accept_3_3 29 58 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58 112 2 14 29 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 58 112
  (Polychromatic418967fa.accept_13_1_6_8_1_208 27 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 58 112 2 13 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 58 112 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 58 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 112 2 12 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 112 (accept_3_3 23 58 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 112 2 11 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 112 (Polychromatic418967fa.accept_15_6_13_7_1_222 21 58 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 112 2 10 29 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 112
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 112 2 9 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 112 (accept_3_3 17 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58
  112 2 8 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  58 112 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 58 112 2 7 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 58 112 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 58 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 112 2 6 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 112 (accept_3_3 11 58 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 112 2 5 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 58 112 (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 58 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 58 112 2 4 29 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 58 112
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 58 112 2 3 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 58 112 (accept_3_3 5 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 112
  2 2 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 58
  112 (Polychromatic418967fa.accept_17_3_7_10_1_3948 3 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 58 112 2 1 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 58 112 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 58 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 112)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 57 112 (Eq.refl Bool.true) (allA_succ_of_accept 55 57 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 55
  57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 57 112
  (Polychromatic418967fa.accept_10_4_7_2_1_211 54 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 57 112 (accept_3_3 53 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  57 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 57 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 112 (accept_3_3 50 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 57 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 112
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 48 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 112 (accept_3_3 47 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 112 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 112 (accept_3_3 44 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 57 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 112
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 112 (accept_3_3 41 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 112 (Polychromatic418967fa.accept_13_1_5_8_1_207 40 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 112 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 112 (accept_3_3 38 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 112
  (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 112 (accept_3_3 35 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 112 (accept_3_3 32 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 57 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 112
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 112 (accept_3_3 29 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 112 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 112 (accept_3_3 26 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 112
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 112 (accept_3_3 23 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 112 (Polychromatic418967fa.accept_20_2_17_12_1_5178 22 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 112 (Polychromatic418967fa.accept_15_6_12_7_1_1360 21 57 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 112 (accept_3_3 20 57 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 57 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 112
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 112 (accept_3_3 17 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 112 (accept_3_3 14 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 112
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 112 (accept_3_3 11 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 112 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 112 (accept_3_3 8 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 57 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 112
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 112 (accept_3_3 5 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  112 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 112 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 57 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 112 (accept_3_3 2 57 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 112))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 112 (allA_of_3_1 56 56 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 112
  (allA_succ_of_accept 54 55 112 (Polychromatic418967fa.accept_23_8_9_20_1_5177 54 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 112 (accept_3_3 53 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 51
  55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 112 (accept_3_3 50 55
  112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 112
  (Polychromatic418967fa.accept_15_4_10_7_1_1356 49 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 112 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 112 (accept_3_3 47 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 112 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 45
  55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 112 (accept_3_3 44 55
  112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 112
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 55 112 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 112 (accept_3_3 41 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 55 112 (Polychromatic418967fa.accept_17_6_4_10_1_5176 40 55 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 112 (accept_3_3 38 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 112 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 112 (Polychromatic418967fa.accept_21_15_13_7_1_5175 36 55 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 112 (accept_3_3 35 55 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 55 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 112 (accept_3_3 32 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 112 (Polychromatic418967fa.accept_13_5_3_8_1_1117 31 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 112 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 112 (accept_3_3 29 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 112 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 55 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 112 (accept_3_3 26 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 112 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 112 (accept_3_3 23 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 112 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 55 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 112 (accept_3_3 20 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 112 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 112 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 112 (accept_3_3 17 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 55 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 112 (accept_3_3 14 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 112 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 112 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 112 (accept_3_3 11 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 112 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 55 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 112 (accept_3_3 8 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  112 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 112 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 112 (accept_3_3 5 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 112 (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 112 (accept_3_3 2 55 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 112 (Polychromatic418967fa.accept_15_1_10_7_1_4087
  1 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  112))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 112 (allA_succ_of_accept 53 54 112
  (accept_3_3 53 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 112 2 26 27 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 112
  (Polychromatic418967fa.accept_12_3_6_4_1_400 51 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 54 112 2 25 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 54 112 (Polychromatic418967fa.accept_13_10_2_8_1_2603 49 54 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 112 2 24 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 112 (accept_3_3 47 54 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 112 2 23 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 112 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 54 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 112 2 22 27 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 112
  (Polychromatic418967fa.accept_15_13_9_7_1_2194 43 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 112 2 21 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 112 (accept_3_3 41 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54
  112 2 20 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  54 112 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 54 112 2 19 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 54 112 (Polychromatic418967fa.accept_10_7_4_2_1_903 37 54 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 112 2 18 27 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 112 (accept_3_3 35 54 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 112 2 17 27 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 112
  (Polychromatic418967fa.accept_12_9_6_4_1_402 33 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 112 2 16 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 54 112 (Polychromatic418967fa.accept_15_1_9_7_1_3130 31 54 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 112 2 15 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 112 (accept_3_3 29 54 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 112 2 14 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 112 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 54 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 112 2 13 27 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 112
  (Polychromatic418967fa.accept_21_4_12_7_1_5174 25 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 112 2 12 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 112 (accept_3_3 23 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54
  112 2 11 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  54 112 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 54 112 2 10 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 54 112 (Polychromatic418967fa.accept_13_6_2_8_1_1782 19 54 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 112 2 9 27 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 112 (accept_3_3 17 54 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 112 2 8 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 112 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 54 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 112 2 7 27 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 112
  (Polychromatic418967fa.accept_15_13_9_7_1_2194 13 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 112 2 6 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 112 (accept_3_3 11 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54
  112 2 5 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  54 112 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 54 112 2 4 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 54 112 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 54 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 112 2 3 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 112 (accept_3_3 5 54 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 112 2 2 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 54 112 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 54 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 112 2 1 27 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 112
  (Polychromatic418967fa.accept_11_1_10_2_1_58 1 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 112)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 112 (allA_of_3_1 53 53 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 112 (allA_succ_of_accept 51 52 112
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 52 112 2 25 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 52 112 (Polychromatic418967fa.accept_11_5_8_2_1_588 49 52 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 112 4 12 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 112 (accept_3_3 47 52 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 112 2 23 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 112 (Polychromatic418967fa.accept_17_11_1_10_1_3925 45 52
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 112 4 11 13 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 112
  (Polychromatic418967fa.accept_17_9_1_10_1_2859 43 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 112 2 21 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 112 (accept_3_3 41 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52
  112 4 10 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  52 112 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 52 112 2 19 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 52 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 52 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 112 4 9 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 112 (accept_3_3 35 52 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 112 2 17 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 112 (Polychromatic418967fa.accept_9_6_7_4_1_212 33
  52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 112 4 8 13 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 112
  (Polychromatic418967fa.accept_17_14_1_10_1_3941 31 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 112 2 15 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 52 112 (accept_3_3 29 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52
  112 4 7 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  52 112 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 52 112 2 13 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 52 112 (Polychromatic418967fa.accept_18_7_16_4_1_1674 25 52 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 112 4 6 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 112 (accept_3_3 23 52 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 112 2 11 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 112 (Polychromatic418967fa.accept_9_3_7_4_1_53 21
  52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 112 4 5 13 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 112
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 112 2 9 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 112 (accept_3_3 17 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  112 4 4 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 112 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 112 2 7 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 52 112 (Polychromatic418967fa.accept_21_13_10_7_1_3701 13 52 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 112 4 3 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 112 (accept_3_3 11 52 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 112 2 5 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 52 112 (Polychromatic418967fa.accept_17_9_1_10_1_2859 9 52 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 112 4 2 13 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 112
  (Polychromatic418967fa.accept_17_7_1_10_1_2836 7 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 52 112 2 3 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 52 112 (accept_3_3 5 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 112
  4 1 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52
  112 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 52 112 2 1 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 52 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 52 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 52 112)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 112
  (allA_succ_of_accept 50 51 112 (accept_3_3 50 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  51 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 112 (accept_3_3 47 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 51 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 112
  (Polychromatic418967fa.accept_18_9_15_4_1_5173 45 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 112 (accept_3_3 44 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 112 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 112 (accept_3_3 41 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 112 (Polychromatic418967fa.accept_13_1_12_8_1_1818 40 51 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 112
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 112 (accept_3_3 38 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 112 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 112 (accept_3_3 35 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 112 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 51 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 112
  (Polychromatic418967fa.accept_10_3_1_2_1_521 33 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 112 (accept_3_3 32 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 112 (accept_3_3 29 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 51 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 112
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 112 (accept_3_3 26 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 112 (Polychromatic418967fa.accept_18_6_15_4_1_3916 24 51 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 112 (accept_3_3 23 51 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 112 (Polychromatic418967fa.accept_13_9_12_8_1_570 22 51 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 112
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 112 (accept_3_3 20 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 112 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 112 (accept_3_3 17 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 112 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 51 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 112
  (Polychromatic418967fa.accept_19_15_13_17_1_5172 15 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 51 112 (accept_3_3 14 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 51 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 112 (accept_3_3 11 51 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 10
  51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 112
  (Polychromatic418967fa.accept_10_9_1_2_1_522 9 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 112 (accept_3_3 8 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  112 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 112 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 112 (accept_3_3 5 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 112 (Polychromatic418967fa.accept_13_4_12_8_1_197 4 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 112 (accept_3_3 2 51 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 51
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  112))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 112 (allA_of_3_1 50 50 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 112 (allA_succ_of_accept 48 49 112 (Polychromatic418967fa.accept_15_3_4_7_1_1352 48
  49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 112 (accept_3_3 47 49
  112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 112
  (Polychromatic418967fa.accept_12_10_1_4_1_392 46 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 49 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 49 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 112 (accept_3_3 44 49 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 49 112 (Polychromatic418967fa.accept_13_4_10_8_1_1817 43 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 49 112 7 6 7 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 49 112 (accept_3_3 41 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 112 (Polychromatic418967fa.accept_15_10_4_7_1_3127 40 49
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 112 (accept_3_3 38 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 112 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 112 (Polychromatic418967fa.accept_17_2_15_10_1_5171 36 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 49 112 7 5 7 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 49 112
  (Polychromatic418967fa.accept_12_10_1_4_1_392 34 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 49 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 112 (accept_3_3 32 49 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 49 112 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 49 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 112 (Polychromatic418967fa.accept_11_8_5_2_1_1629
  30 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 112 (accept_3_3 29
  49 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 49 112 7 4 7 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 49 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 112 (accept_3_3 26 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 112 (Polychromatic418967fa.accept_13_12_10_8_1_3343 25 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 112 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 112 (accept_3_3 23 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 112 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 49 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 49 112 7 3 7 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 49 112 (accept_3_3 20 49 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 112 (Polychromatic418967fa.accept_11_8_5_2_1_1629
  19 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 112
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 112 (accept_3_3 17 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 112 (Polychromatic418967fa.accept_25_16_24_12_1_5170 16 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 49 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 49 112 7 2 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 49 112
  (Polychromatic418967fa.accept_19_13_11_17_1_5152 13 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 112 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 112 (accept_3_3 11 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 112 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 49 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 112 (accept_3_3 8 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 49 112
  7 1 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 49 112
  (Polychromatic418967fa.accept_19_6_11_17_1_2611 6 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 112 (accept_3_3 5 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  112 (Polychromatic418967fa.accept_13_4_10_8_1_1817 4 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 49 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 112 (accept_3_3 2 49 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 112 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 112)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 112 (allA_succ_of_accept 47 48 112 (accept_3_3 47 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 112 2 23 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 48 112 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 48 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 112 4 11 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 43
  48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 112 2 21 24 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 112 (accept_3_3 41
  48 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 112 8 5 6 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 112
  (Polychromatic418967fa.accept_11_6_4_2_1_599 39 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 48 112 2 19 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 48 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 48 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 112 4 9 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 112 (accept_3_3 35 48 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 48 112 2 17 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 48 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 48 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 112 16 2 3 7 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 112
  (Polychromatic418967fa.accept_11_9_4_2_1_600 31 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 112 2 15 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 112 (accept_3_3 29 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48
  112 4 7 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  48 112 (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 48 112 2 13 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 48 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 48 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 112 8 3 6 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 112 (accept_3_3 23 48 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 112 2 11 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 112 (Polychromatic418967fa.accept_19_2_10_17_1_3876
  21 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 112 4 5 12 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 112
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 112 2 9 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 112 (accept_3_3 17 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48
  112 16 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  48 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 48 112 2 7 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 48 112 (Polychromatic418967fa.accept_17_13_14_10_1_1847 13 48 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 112 4 3 12 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 112 (accept_3_3 11 48 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 112 2 5 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 112 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 48 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 112 8 1 6 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 112
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 112 2 3 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 112 (accept_3_3 5 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 112
  4 1 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48
  112 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 48 112 2 1 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 48 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 48 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 112)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 112 (allA_of_3_1 47 47 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 112 (allA_succ_of_accept 45 46
  112 (Polychromatic418967fa.accept_20_5_6_12_1_2444 45 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 46 112 2 22 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 46 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 46 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 112 2 21 23 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 112 (accept_3_3 41 46 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 112 2 20 23 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 112
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 46 112 2 19 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 46 112 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 46 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 112 2 18 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 112 (accept_3_3 35 46 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 112 2 17 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 112 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 46 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 112 2 16 23 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 112
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 112 2 15 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 46 112 (accept_3_3 29 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46
  112 2 14 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  46 112 (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 46 112 2 13 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 46 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 46 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 112 2 12 23 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 112 (accept_3_3 23 46 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 112 2 11 23 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 112
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 112 2 10 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 112 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 46 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 112 2 9 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 112 (accept_3_3 17 46 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 112 2 8 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 112 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 46 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 112 2 7 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 112 (Polychromatic418967fa.accept_12_1_10_4_1_380
  13 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 112 2 6 23 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 112 (accept_3_3 11
  46 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 112 2 5 23 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 112
  (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 112 2 4 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 46 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 112 2 3 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 112 (accept_3_3 5 46 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 112 2 2 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 112 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 46 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 112 2 1 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 112 (Polychromatic418967fa.accept_10_1_6_2_1_867 1
  46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  112)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 112 (allA_succ_of_accept 44 45 112 (accept_3_3 44 45
  112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 112 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 112
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 112 (accept_3_3 41 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  45 112 (Polychromatic418967fa.accept_13_1_6_8_1_208 40 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 112 (Polychromatic418967fa.accept_22_17_1_2_1_5169 39 45 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 112 (accept_3_3 38 45 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 112
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 112 (accept_3_3 35 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 112 (Polychromatic418967fa.accept_19_15_7_17_1_5168 34 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 112 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 112 (accept_3_3 32 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 45 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 112
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 112 (accept_3_3 29 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 112 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 112 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 112 (accept_3_3 26 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 112
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 24 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 112 (accept_3_3 23 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 112 (Polychromatic418967fa.accept_21_1_3_7_1_3727 22 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 112 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 45 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 112 (accept_3_3 20 45 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 45 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 112
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 112 (accept_3_3 17 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 112 (Polychromatic418967fa.accept_19_16_7_17_1_3853 16 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 112 (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 112 (accept_3_3 14 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 112
  (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 112 (accept_3_3 11 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 112 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 112 (Polychromatic418967fa.accept_19_9_7_17_1_3875 9 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 112 (accept_3_3 8 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 45 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 112
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 112 (accept_3_3 5 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  112 (Polychromatic418967fa.accept_17_4_11_10_1_5167 4 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 112 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 112 (accept_3_3 2 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 112)))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 44 112 (allA_of_3_1 44 44 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 112
  (allA_succ_of_accept 42 43 112 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 43 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 112 (accept_3_3 41 43 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 43 112 (Polychromatic418967fa.accept_19_2_5_17_1_3850 40 43 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 112 (accept_3_3 38 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 112 (Polychromatic418967fa.accept_13_10_4_8_1_2570 36 43 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 112 (accept_3_3 35 43 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 112 (Polychromatic418967fa.accept_11_1_10_2_1_58 34 43 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 112 (accept_3_3 32 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 112 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 112 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 43 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 112 (accept_3_3 29 43 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 43 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 112 (accept_3_3 26 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 112 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 112 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 43 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 112 (accept_3_3 23 43 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 112 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 43 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 112 (accept_3_3 20 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 112 (Polychromatic418967fa.accept_17_1_9_10_1_1864 18 43 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 112 (accept_3_3 17 43 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 112 (Polychromatic418967fa.accept_17_16_9_10_1_3962 16 43
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 112 (accept_3_3 14 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 112 (Polychromatic418967fa.accept_17_13_9_10_1_2888 13 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 112 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 43 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 112 (accept_3_3 11 43 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 43 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 112 (accept_3_3 8 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  112 (Polychromatic418967fa.accept_19_7_5_17_1_3849 7 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 43 112 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 43 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 112 (accept_3_3 5 43 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 112 (Polychromatic418967fa.accept_21_4_1_7_1_3771 4 43 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 43 112 (accept_3_3 2 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43
  112 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 43 112))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 112 (allA_succ_of_accept 41 42 112
  (accept_3_3 41 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 112 2 20 21 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 112
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 112 2 19 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 42 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 112 2 18 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 42 112 7 5 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 42 112 2 17 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 112 (Polychromatic418967fa.accept_12_9_6_4_1_402 33
  42 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 112 2 16 21 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 112
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 31 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 112 2 15 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 112 (accept_3_3 29 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42
  112 14 2 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  42 112 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 42 112 2 13 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 42 112 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 42 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 112 2 12 21 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 112 (accept_3_3 23 42 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 112 2 11 21 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 112 7 3 6 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 112 2 10 21 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 112
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 112 2 9 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 112 (accept_3_3 17 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42
  112 2 8 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  42 112 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 42 112 14 1 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 42 112 (Polychromatic418967fa.accept_19_13_4_17_1_5166 13 42 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 112 2 6 21 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 112 (accept_3_3 11 42 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 112 2 5 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 112 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 42 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 112 2 4 21 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 42 112 7 1 6 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 42 112 2 3 21 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 112 (accept_3_3 5 42 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 112 2 2 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 42
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 112 2 1 21 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 112
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 112)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 112 (allA_of_3_1 41 41 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 40 112 (allA_succ_of_accept 39 40 112
  (Polychromatic418967fa.accept_21_18_19_7_1_5165 39 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 112 2 19 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 112 (Polychromatic418967fa.accept_13_11_1_8_1_1776 37 40 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 112 4 9 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 112 (accept_3_3 35 40 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 40 112 2 17 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 40 112 (Polychromatic418967fa.accept_13_7_1_8_1_1778 33 40 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 112 8 4 5 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 112
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 112 2 15 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 112 (accept_3_3 29 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  112 4 7 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 112 (Polychromatic418967fa.accept_15_12_10_7_1_1357 27 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 112 2 13 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 40 112 (Polychromatic418967fa.accept_13_12_1_8_1_1779 25 40 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 112 8 3 5 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 112 (accept_3_3 23 40 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 112 2 11 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 112 (Polychromatic418967fa.accept_17_4_6_10_1_5164
  21 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 112 4 5 10 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 112
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 19 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 40 112 2 9 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 40 112 (accept_3_3 17 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40
  112 8 2 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  40 112 (Polychromatic418967fa.accept_19_15_2_17_1_5163 15 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 40 112 2 7 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 40 112 (Polychromatic418967fa.accept_21_13_19_7_1_5162 13 40 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 112 4 3 10 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 112 (accept_3_3 11 40 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 112 2 5 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 112 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 40 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 112 8 1 5 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 112
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 40 112 2 3 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 40 112 (accept_3_3 5 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 112
  4 1 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40
  112 (Polychromatic418967fa.accept_15_3_10_7_1_2196 3 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 40 112 2 1 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 40 112 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 40 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 112)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 112
  (allA_succ_of_accept 38 39 112 (accept_3_3 38 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  39 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 39 112 (Polychromatic418967fa.accept_21_15_18_7_1_5161 36 39 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 112 (accept_3_3 35 39 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 39 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 112
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 39 112 (accept_3_3 32 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  39 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 39 112 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 39 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 112 (accept_3_3 29 39 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 39 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 112
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 112 (accept_3_3 26 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  39 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 39 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 112 (accept_3_3 23 39 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 112 (Polychromatic418967fa.accept_19_3_1_17_1_5159 22 39 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 112
  (Polychromatic418967fa.accept_10_1_9_2_1_45 21 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 112 (accept_3_3 20 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  39 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 112 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 39 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 112 (accept_3_3 17 39 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 39 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 112
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 112 (accept_3_3 14 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  39 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 39 112 (Polychromatic418967fa.accept_17_12_5_10_1_5160 12 39 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 112 (accept_3_3 11 39 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 39 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 112
  (Polychromatic418967fa.accept_19_9_1_17_1_3879 9 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 112 (accept_3_3 8 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  112 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 39 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 112 (accept_3_3 5 39 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 112 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 39 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 112 (Polychromatic418967fa.accept_19_3_1_17_1_5159
  3 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 112 (accept_3_3 2 39
  112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  112))))))))))))))))))))))))))))))))))))))) (allB_succ 38 112 (allA_of_3_1 38 38 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 112 (allA_succ_of_accept 36 37 112 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 37 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 112 (accept_3_3 35 37 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 34
  37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 112 (accept_3_3 32 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 112 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 112 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 37 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 112 (accept_3_3 29 37 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 112 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 37 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 112 (accept_3_3 26 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 112 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 37 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 112 (accept_3_3 23 37 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 112 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 37 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 112 (accept_3_3 20 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 112 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 112 (Polychromatic418967fa.accept_26_18_11_8_1_5158 18 37 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 112 (accept_3_3 17 37 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 112 (accept_3_3 14 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 112 (Polychromatic418967fa.accept_17_13_3_10_1_5157 13 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 112 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 37 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 112 (accept_3_3 11 37 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 112 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 37 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 112 (accept_3_3 8 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  112 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 112 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 37 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 112 (accept_3_3 5 37 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 112 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 37 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 37
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 112 (accept_3_3 2 37 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 112 (Polychromatic418967fa.accept_13_1_11_8_1_2562
  1 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37
  112))))))))))))))))))))))))))))))))))))) (allB_succ 36 112 (allA_succ_of_accept 35 36 112 (accept_3_3 35 36 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 112 2 17 18 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 112
  (Polychromatic418967fa.accept_13_7_10_8_1_567 33 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 36 112 4 8 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 112 (Polychromatic418967fa.accept_10_1_6_2_1_867 31 36 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 112 2 15 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 112 (accept_3_3 29 36 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 112 4 7 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 36 112 (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 36 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 112 2 13 18 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 112
  (Polychromatic418967fa.accept_13_12_10_8_1_3343 25 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 112 4 6 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 112 (accept_3_3 23 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36
  112 2 11 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  36 112 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 36 112 4 5 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 36 112 (Polychromatic418967fa.accept_21_19_15_7_1_3709 19 36 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 112 2 9 18 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 112 (accept_3_3 17 36 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 112 4 4 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 112 (Polychromatic418967fa.accept_13_2_10_8_1_1126 15 36 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 112 2 7 18 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 112
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 112 4 3 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 112 (accept_3_3 11 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36
  112 2 5 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  36 112 (Polychromatic418967fa.accept_21_9_15_7_1_5156 9 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 36 112 4 2 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 36 112 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 36 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 112 2 3 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 112 (accept_3_3 5 36 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 112 4 1 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 36 112 (Polychromatic418967fa.accept_21_3_15_7_1_5155 3 36 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 112 2 1 18 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 112
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 112)))))))))))))))))))))))))))))))))))) (allB_succ 35 112 (allA_of_3_1 35 35 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 34 112 (allA_succ_of_accept 33 34 112 (Polychromatic418967fa.accept_9_6_7_4_1_212 33
  34 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 34 112 2 16 17 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 34 112
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 34 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 34 112 2 15 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 34 112 (accept_3_3 29 34 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34
  112 2 14 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  34 112 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 34 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 34 112 2 13 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 34 112 (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 34 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 112 2 12 17 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 112 (accept_3_3 23 34 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 112 2 11 17 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 112
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 34 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 112 2 10 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 34 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 112 2 9 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 112 (accept_3_3 17 34 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 112 2 8 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 112 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 34 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 112 2 7 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 112 (Polychromatic418967fa.accept_12_1_10_4_1_380
  13 34 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 112 2 6 17 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 112 (accept_3_3 11
  34 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 112 2 5 17 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 112
  (Polychromatic418967fa.accept_21_9_13_7_1_5154 9 34 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 112 2 4 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 112 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 34 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 112 2 3 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 112 (accept_3_3 5 34 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 112 2 2 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 112 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 34 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 112 2 1 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 34
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 112))))))))))))))))))))))))))))))))))
  (allB_succ 33 112 (allA_succ_of_accept 32 33 112 (accept_3_3 32 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 33 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 33 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 112 (accept_3_3 29 33 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 28
  33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 112
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 112 (accept_3_3 26 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 112 (Polychromatic418967fa.accept_17_7_16_10_1_1849 24 33 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 112 (accept_3_3 23 33 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 112 (Polychromatic418967fa.accept_13_9_7_8_1_1122 22 33 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 112
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 112 (accept_3_3 20 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 112 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 33 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 112 (accept_3_3 17 33 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 112 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 33 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 112
  (Polychromatic418967fa.accept_10_5_3_2_1_899 15 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 112 (accept_3_3 14 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 33 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 112 (accept_3_3 11 33 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 33 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 112
  (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 112 (accept_3_3 8 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  112 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 112 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 33 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 112 (accept_3_3 5 33 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 112 (Polychromatic418967fa.accept_15_4_3_7_1_713 4 33 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 112 (accept_3_3 2 33 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 112)))))))))))))))))))))))))))))))))
  (allB_succ 32 112 (allA_of_3_1 32 32 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 112
  (allA_succ_of_accept 30 31 112 (Polychromatic418967fa.accept_17_13_14_10_1_1847 30 31 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 112 (accept_3_3 29 31 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 112 (Polychromatic418967fa.accept_18_10_13_4_1_5153 28 31 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 31 112 (accept_3_3 26 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  31 112 (Polychromatic418967fa.accept_13_12_5_8_1_1101 25 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 31 112 (Polychromatic418967fa.accept_15_9_1_7_1_1350 24 31 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 112 (accept_3_3 23 31 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 112 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 31 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 112 (accept_3_3 20 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  31 112 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 31 112 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 31 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 112 (accept_3_3 17 31 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 112 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 31 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 112 (accept_3_3 14 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  31 112 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 112 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 31 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 112 (accept_3_3 11 31 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 112 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 31 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 112 (accept_3_3 8 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  112 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 112 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 31 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 112 (accept_3_3 5 31 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 112 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 31 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 112 (accept_3_3 2 31 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 112 (Polychromatic418967fa.accept_13_1_5_8_1_207 1
  31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 112)))))))))))))))))))))))))))))))
  (allB_succ 30 112 (allA_succ_of_accept 29 30 112 (accept_3_3 29 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 112 2 14 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 30 112 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 30 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 112 2 13 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 25
  30 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 112 2 12 15 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 112 (accept_3_3 23
  30 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 112 2 11 15 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 112
  (Polychromatic418967fa.accept_12_9_6_4_1_402 21 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 112 2 10 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 30 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 112 2 9 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 112 (accept_3_3 17 30 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 112 2 8 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 30 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 112 2 7 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 112
  (Polychromatic418967fa.accept_19_13_11_17_1_5152 13 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 30 112 2 6 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 30 112 (accept_3_3 11 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 112 2 5 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 112 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 30 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 112 2 4 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 30 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 112 2 3 15 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 112 (accept_3_3 5 30 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 112 2 2 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 112 (Polychromatic418967fa.accept_12_3_6_4_1_400 3
  30 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 112 2 1 15 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 112
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 112)))))))))))))))))))))))))))))) (allB_succ 29 112 (allA_of_3_1 29 29 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 28 112 (allA_succ_of_accept 27 28 112 (Polychromatic418967fa.accept_19_8_9_17_1_5151 27 28 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 112 2 13 14 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 112
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 28 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 28 112 4 6 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 28 112 (accept_3_3 23 28 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28
  112 2 11 14 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 28
  112 7 3 4 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 28
  112 4 5 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19
  28 112 (Polychromatic418967fa.accept_13_6_2_8_1_1782 19 28 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 28 112 2 9 14 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 28 112 (accept_3_3 17 28 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 28 112 4 4 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 28 112 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 28 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 112 14 1 2 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 112 (Polychromatic418967fa.accept_18_13_10_4_1_5150 13 28
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 112 4 3 7 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 112 (accept_3_3 11
  28 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 112 2 5 14 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 112
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 28 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 28 112 4 2 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 28 112 7 1 4 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 28 112 2 3 14 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 28 112 (accept_3_3 5 28 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 112
  4 1 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 112
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 28 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 112 2 1 14 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 112 (Polychromatic418967fa.accept_17_1_11_10_1_5149 1 28 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 112)))))))))))))))))))))))))))) (allB_succ 27 112 (allA_succ_of_accept 26
  27 112 (accept_3_3 26 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 112
  (Polychromatic418967fa.accept_6_1_3_4_1_1 25 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 27 112 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 27 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 112 (accept_3_3 23 27 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 27 112 (Polychromatic418967fa.accept_13_9_1_8_1_1742 22 27 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 112 (Polychromatic418967fa.accept_15_6_12_7_1_1360
  21 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 112 (accept_3_3 20
  27 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 112
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 27 112 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 27 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 112 (accept_3_3 17 27 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 27 112 (Polychromatic418967fa.accept_19_16_8_17_1_5148 16 27 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 112
  (Polychromatic418967fa.accept_10_5_7_2_1_516 15 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 112 (accept_3_3 14 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 112 (Polychromatic418967fa.accept_13_12_1_8_1_1779 12 27 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 112 (accept_3_3 11 27 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 112 (Polychromatic418967fa.accept_15_10_12_7_1_1358 10 27
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 112
  (Polychromatic418967fa.accept_10_9_7_2_1_887 9 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 112 (accept_3_3 8 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  112 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 112 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 27 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 112 (accept_3_3 5 27 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 112 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 27 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 112 (Polychromatic418967fa.accept_15_3_12_7_1_1346
  3 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 112 (accept_3_3 2 27
  112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 112)))))))))))))))))))))))))))
  (allB_succ 26 112 (allA_of_3_1 26 26 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 112
  (allA_succ_of_accept 24 25 112 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 25 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 112 (accept_3_3 23 25 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 112 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 25 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 112 (accept_3_3 20 25
  112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 112 (Polychromatic418967fa.accept_9_1_7_4_1_52
  19 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 112
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 112 (accept_3_3 17 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 112 (Polychromatic418967fa.accept_15_1_10_7_1_4087 16 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 25 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 112 (accept_3_3 14 25 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 112 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 25 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 112
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 112 (accept_3_3 11 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 112 (accept_3_3 8 25 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 112 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 25 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 112
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 112 (accept_3_3 5 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  112 (Polychromatic418967fa.accept_13_4_12_8_1_197 4 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 25 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 25 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 112 (accept_3_3 2 25 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 25 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 112))))))))))))))))))))))))) (allB_succ 24 112
  (allA_succ_of_accept 23 24 112 (accept_3_3 23 24 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24
  112 2 11 12 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  24 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 24 112 4 5 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 24 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 24 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 112 2 9 12 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 112 (accept_3_3 17 24 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 112 8 2 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 24 112 (Polychromatic418967fa.accept_18_15_6_4_1_5147 15 24 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 112 2 7 12 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 112
  (Polychromatic418967fa.accept_15_13_9_7_1_2194 13 24 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 112 4 3 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 112 (accept_3_3 11 24 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24
  112 2 5 12 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  24 112 (Polychromatic418967fa.accept_13_9_11_8_1_195 9 24 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 24 112 8 1 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 24 112 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 112 2 3 12 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 112 (accept_3_3 5 24 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 112 4 1 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 24 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 24 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 112 2 1 12 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 112
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 24 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 112)))))))))))))))))))))))) (allB_succ 23 112 (allA_of_3_1 23 23 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 22 112 (allA_succ_of_accept 21 22 112 (Polychromatic418967fa.accept_19_2_3_17_1_5146 21 22 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 112 2 10 11 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 112
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 22 112 2 9 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 22 112 (accept_3_3 17 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22
  112 2 8 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  22 112 (Polychromatic418967fa.accept_17_15_5_10_1_5145 15 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 22 112 2 7 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 22 112 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 22 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 112 2 6 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 112 (accept_3_3 11 22 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 112 2 5 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 22 112 (Polychromatic418967fa.accept_20_9_2_12_1_5144 9 22 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 22 112 2 4 11 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 22 112
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 22 112 2 3 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 22 112 (accept_3_3 5 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 112
  2 2 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 22
  112 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 22 112 2 1 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 22 112 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 22 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 112)))))))))))))))))))))) (allB_succ 21 112 (allA_succ_of_accept
  20 21 112 (accept_3_3 20 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 112
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 21 112 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 21 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 112 (accept_3_3 17 21 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 21 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 15
  21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 21 112 7 2 3 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 21 112
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 21 112 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 21 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 112 (accept_3_3 11 21 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 21 112 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 21 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 112 (Polychromatic418967fa.accept_10_9_1_2_1_522 9
  21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 112 (accept_3_3 8 21 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 112 7 1 3 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 21 112 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 21
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 112 (accept_3_3 5 21 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 112 (Polychromatic418967fa.accept_19_4_2_17_1_3870
  4 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 112
  (Polychromatic418967fa.accept_10_3_1_2_1_521 3 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 112 (accept_3_3 2 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21
  112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 112))))))))))))))))))))) (allB_succ 20 112 (allA_of_3_1 20 20 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 19 112 (allA_succ_of_accept 18 19 112 (Polychromatic418967fa.accept_15_3_4_7_1_1352 18 19 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 112 (accept_3_3 17 19 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 112 (Polychromatic418967fa.accept_9_7_1_4_1_217 16
  19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 19 112 (accept_3_3 14 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  19 112 (Polychromatic418967fa.accept_20_13_19_12_1_5143 13 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 19 112 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 19 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 112 (accept_3_3 11 19 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 112 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 19 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 112
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 112 (accept_3_3 8 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19
  112 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 19 112 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 19 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 112 (accept_3_3 5 19 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 19 112 (Polychromatic418967fa.accept_21_4_19_7_1_5142 4 19 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 112 (accept_3_3 2 19 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 112 (Polychromatic418967fa.accept_10_1_9_2_1_45 1
  19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 112))))))))))))))))))) (allB_succ 18
  112 (allA_succ_of_accept 17 18 112 (accept_3_3 17 18 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  18 112 2 8 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 18 112 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 18 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 18 112 2 7 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 112 (Polychromatic418967fa.accept_19_13_18_17_1_5141 13 18 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 112 2 6 9 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 112 (accept_3_3 11 18 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 112 2 5 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 18 112 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 18 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 112 2 4 9 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 112
  (Polychromatic418967fa.accept_17_7_1_10_1_2836 7 18 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 112 2 3 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 112 (accept_3_3 5 18 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 112
  2 2 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 112
  (Polychromatic418967fa.accept_12_3_6_4_1_400 3 18 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 112 2 1 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 112 (Polychromatic418967fa.accept_13_1_5_8_1_207 1 18 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 112)))))))))))))))))) (allB_succ 17 112 (allA_of_3_1 17 17 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 112 (allA_succ_of_accept 15 16 112
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 16 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 112 2 7 8 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 112 (Polychromatic418967fa.accept_19_13_16_17_1_5140 13 16 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 112 4 3 4 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 112 (accept_3_3 11 16 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 112 2 5 8 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 112 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 16 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 112 8 1 2 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 112 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7
  16 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 112 2 3 8 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 112 (accept_3_3 5 16
  112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 112 4 1 4 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 112
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 16 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 112 2 1 8 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 16 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 112)))))))))))))))) (allB_succ 15 112 (allA_succ_of_accept 14 15 112
  (accept_3_3 14 15 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 112
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 15 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 15 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 112 (accept_3_3 11 15 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 15 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 112 (Polychromatic418967fa.accept_11_9_4_2_1_600 9
  15 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 112 (accept_3_3 8 15 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 112
  (Polychromatic418967fa.accept_11_6_4_2_1_599 6 15 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 112 (accept_3_3 5 15 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  112 (Polychromatic418967fa.accept_17_4_15_10_1_5139 4 15 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 112 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 15 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 112 (accept_3_3 2 15 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 15 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 112))))))))))))))) (allB_succ 14 112 (allA_of_3_1 14
  14 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 112 (allA_succ_of_accept 12 13 112
  (Polychromatic418967fa.accept_24_12_13_16_1_5138 12 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 13 112 (accept_3_3 11 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 13 112 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 13 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 112 (accept_3_3 8 13 112
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 112 (Polychromatic418967fa.accept_18_7_13_4_1_1670
  7 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 112
  (Polychromatic418967fa.accept_15_6_13_7_1_222 6 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 112 (accept_3_3 5 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  112 (Polychromatic418967fa.accept_19_4_13_17_1_5137 4 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 13 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 112 (accept_3_3 2 13 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 112 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 13 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 112))))))))))))) (allB_succ 12 112
  (allA_succ_of_accept 11 12 112 (accept_3_3 11 12 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12
  112 2 5 6 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12
  112 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 12 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 12 112 4 2 3 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 12 112 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 12 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 112 2 3 6 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 112 (accept_3_3 5 12 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 112 4 1 3 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 12 112 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 12 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 112 2 1 6 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 112
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 12 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 112)))))))))))) (allB_succ 11 112 (allA_of_3_1 11 11 112 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 112 (allA_succ_of_accept 9 10 112 (Polychromatic418967fa.accept_21_9_10_7_1_383 9 10 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 112 2 4 5 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 112
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 10 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 112 2 3 5 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 112 (accept_3_3 5 10 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 112
  2 2 5 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 112
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 10 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 112 2 1 5 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 112 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 10 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 112)))))))))) (allB_succ 9 112 (allA_succ_of_accept 8 9 112 (accept_3_3 8
  9 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 112 (Polychromatic418967fa.accept_6_1_3_4_1_1
  7 9 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 112
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 9 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 112 (accept_3_3 5 9 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 112
  (Polychromatic418967fa.accept_11_4_9_2_1_259 4 9 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 112 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 9 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 112 (accept_3_3 2 9 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 112))))))))) (allB_succ 8 112 (allA_of_3_1 8 8 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 112 (allA_succ_of_accept 6 7 112
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 7 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 112 (accept_3_3 5 7 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 112
  (Polychromatic418967fa.accept_10_4_7_2_1_211 4 7 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 112 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 112 (accept_3_3 2 7 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 112 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 7 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 112))))))) (allB_succ 6 112 (allA_succ_of_accept 5 6 112
  (accept_3_3 5 6 112 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 112 2 2 3 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 112
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 6 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 112 2 1 3 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 112 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 6 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 112)))))) (allB_succ 5 112 (allA_of_3_1 5 5 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 112 (allA_succ_of_accept 3 4 112 (Polychromatic418967fa.accept_15_3_4_7_1_1352 3 4
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 112 2 1 2 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 112
  (Polychromatic418967fa.accept_19_1_4_17_1_5136 1 4 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 112)))) (allB_succ 3 112 (allA_succ_of_accept 2 3 112 (accept_3_3 2 3 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 112 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 3 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 112))) (allB_succ 2 112 (allA_of_3_1 2 2 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  112))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


