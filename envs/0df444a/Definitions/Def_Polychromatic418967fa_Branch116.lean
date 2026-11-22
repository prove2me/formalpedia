-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch116
-- name    : Polychromatic418967fa_Branch116
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:11:20.694779+00:00
-- url     : https://prove2.me/theorems/e9de2561-5fd2-4fe0-924a-32e1765a03b8
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

def Polychromatic418967fa.branch_116 : allB 116 116 :=
  allB_succ' 2 115 116 (Eq.refl Bool.true) (allA_of_3_0 2 115 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  114 116 (Eq.refl Bool.true) (allA_succ_of_gcd 2 114 116 2 1 57 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 116 (accept_3_2 1 114 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 114 116))) (allB_succ' 4 113 116 (Eq.refl Bool.true) (allA_succ_of_accept 3 113 116
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 113 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 113 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 113 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 116 (accept_3_2 1 113 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 113 116)))) (allB_succ' 5 112 116 (Eq.refl Bool.true) (allA_of_3_0 5 112 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 111 116 (Eq.refl Bool.true) (allA_succ_of_accept 5 111 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 111 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 116 (accept_3_2 4 111 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 111 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 111 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 116 (accept_3_2 1 111 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111 116)))))) (allB_succ' 7 110 116 (Eq.refl Bool.true) (allA_succ_of_gcd 6 110 116 2 3
  55 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 110 116
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 110 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 110 116 2 2 55 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 110 116 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 110 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 116 2 1 55 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 116 (accept_3_2 1 110 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 110 116))))))) (allB_succ' 8 109 116 (Eq.refl Bool.true) (allA_of_3_0 8 109 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 108 116 (Eq.refl Bool.true) (allA_succ_of_gcd 8 108 116 4 2 27 29
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 116
  (accept_3_2 7 108 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 116 2 3 54 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 116
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 5 108 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 108 116 4 1 27 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 108 116 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 108 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 116 2 1 54 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 116 (accept_3_2 1 108 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 108 116))))))))) (allB_succ' 10 107 116 (Eq.refl Bool.true) (allA_succ_of_accept 9 107 116
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 107 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 107 116 (Polychromatic418967fa.accept_16_8_11_4_1_3290 8 107 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 116 (accept_3_2 7 107 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 107 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 107 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 116 (Polychromatic418967fa.accept_7_5_2_4_1_126 5
  107 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 116 (accept_3_2 4 107
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 116 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 107 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 116
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 107 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 116 (accept_3_2 1 107 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  116)))))))))) (allB_succ' 11 106 116 (Eq.refl Bool.true) (allA_of_3_0 11 106 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 105 116 (Eq.refl Bool.true) (allA_succ_of_accept 11 105 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 105 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 116 (accept_3_2 10 105 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 116 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 105 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 116 (Polychromatic418967fa.accept_13_8_1_12_1_762 8 105 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 116 (accept_3_2 7 105 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 116 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 105 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 116 (accept_3_2 4 105 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 116 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 105 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 116 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 105 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 116 (accept_3_2 1 105 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105 116)))))))))))) (allB_succ' 13 104 116 (Eq.refl Bool.true) (allA_succ_of_gcd 12 104
  116 4 3 26 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  104 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 104 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 104 116 2 5 52 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 104 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 104 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 116 4 2 26 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 116 (accept_3_2 7 104 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104 116 2 3 52 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 104 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 104 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 116 4 1 26 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 116
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 104 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 104 116 2 1 52 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 104 116 (accept_3_2 1 104 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  116))))))))))))) (allB_succ' 14 103 116 (Eq.refl Bool.true) (allA_of_3_0 14 103 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 102 116 (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 116 2 7 51 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 116 (accept_3_2 13 102 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 116 2 6 51 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 116
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 102 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 116 2 5 51 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 102 116 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 102 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 116 2 4 51 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 116 (accept_3_2 7 102 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 102 116 2 3 51 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 102 116 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 102 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 116 2 2 51 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 102 116 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  102 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 116 2 1 51 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 116 (accept_3_2 1
  102 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 116))))))))))))))) (allB_succ' 16 101 116 (Eq.refl
  Bool.true) (allA_succ_of_accept 15 101 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 101 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 116 (Polychromatic418967fa.accept_9_5_2_8_1_109
  14 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 116 (accept_3_2 13
  101 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 116
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 101 116 (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 101 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 116 (accept_3_2 10 101 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 116
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 116 (accept_3_2 7 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 116 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 101 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 116 (accept_3_2 4 101 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 116
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 116 (accept_3_2 1 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  116)))))))))))))))) (allB_succ' 17 100 116 (Eq.refl Bool.true) (allA_of_3_0 17 100 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 99 116 (Eq.refl Bool.true) (allA_succ_of_accept 17 99 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 116 (accept_3_2 16 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 116 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 116 (Polychromatic418967fa.accept_13_1_8_12_1_2045 14 99 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 116 (accept_3_2 13 99 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 99 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 116 (accept_3_2 10 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 116 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 99 116 (Polychromatic418967fa.accept_16_8_3_4_1_3233 8 99 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 116 (accept_3_2 7 99 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 116 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 99 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 116 (accept_3_2 4 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  116 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 116 (Polychromatic418967fa.accept_15_2_9_11_1_1551 2 99 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 116 (accept_3_2 1 99 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 116)))))))))))))))))) (allB_succ' 19 98 116 (Eq.refl Bool.true) (allA_succ_of_gcd 18 98 116 2
  9 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 98 116
  (Polychromatic418967fa.accept_12_5_2_8_1_172 17 98 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 98 116 2 8 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 98 116 (Polychromatic418967fa.accept_20_15_18_16_1_5441 15 98 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 116 2 7 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 116 (accept_3_2 13 98 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 98 116 2 6 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 98 116 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 98 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 98 116 2 5 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 98 116 (Polychromatic418967fa.accept_27_9_17_8_1_5440 9
  98 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 116 2 4 49 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 116 (accept_3_2 7 98
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 116 2 3 49 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 98 116
  (Polychromatic418967fa.accept_11_5_10_6_1_793 5 98 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 98 116 2 2 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 98 116 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 98 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 116 2 1 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 116 (accept_3_2 1 98 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 98 116))))))))))))))))))) (allB_succ' 20 97 116 (Eq.refl Bool.true) (allA_of_3_0 20 97 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 96 116 (Eq.refl Bool.true) (allA_succ_of_gcd 20 96 116 4 5 24
  29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 116
  (accept_3_2 19 96 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 116 2 9 48 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 116
  (Polychromatic418967fa.accept_13_4_5_12_1_751 17 96 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 96 116 4 4 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 96 116 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 96 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 116 2 7 48 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 116 (accept_3_2 13 96 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 96 116 4 3 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 96 116 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 96 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 116 2 5 48 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 96
  116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 116 4 2 24 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 116 (accept_3_2 7 96
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 116 2 3 48 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 116
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 116 4 1 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 96 116 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 96 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 116 2 1 48 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 116 (accept_3_2 1 96 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96 116))))))))))))))))))))) (allB_succ' 22 95 116 (Eq.refl Bool.true) (allA_succ_of_accept 21 95
  116 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 95 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 95 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 116 (accept_3_2 19 95 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 95 116 (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 95 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 116
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 116 (accept_3_2 16 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 116 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 95 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 116 (accept_3_2 13 95 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 116 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 95 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 116
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 116 (accept_3_2 10 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 116 (Polychromatic418967fa.accept_13_8_4_12_1_2753 8 95 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 116 (accept_3_2 7 95 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 116 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 95 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 116
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 5 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 116 (accept_3_2 4 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 95 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 116 (accept_3_2 1 95 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95 116)))))))))))))))))))))) (allB_succ' 23 94 116 (Eq.refl Bool.true) (allA_of_3_0 23 94 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 93 116 (Eq.refl Bool.true) (allA_succ_of_accept 23 93 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 116 (accept_3_2 22 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  93 116 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 93 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 93 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 116 (accept_3_2 19 93 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 116 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 93 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 116 (accept_3_2 16 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  93 116 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 93 116 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 93 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 116 (accept_3_2 13 93 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 116 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 93 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 116 (accept_3_2 10 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  93 116 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 93 116 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 93 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 116 (accept_3_2 7 93 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 93 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 116 (accept_3_2 4 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  116 (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 93 116 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 93 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 116 (accept_3_2 1 93 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 93 116)))))))))))))))))))))))) (allB_succ' 25 92 116 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 92 116 4 6 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 92 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 92 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 116 2 11 46 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 116 (Polychromatic418967fa.accept_9_3_2_8_1_108 21
  92 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 116 4 5 23 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 116 (accept_3_2 19
  92 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92 116 2 9 46 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 92 116
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 92 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 92 116 4 4 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 92 116 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 92 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 116 2 7 46 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 116 (accept_3_2 13 92 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 92 116 4 3 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 92 116 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 92 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 116 2 5 46 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 116 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9
  92 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 116 4 2 23 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 116 (accept_3_2 7 92
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 116 2 3 46 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92 116
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 92 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 116 4 1 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 92 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 116 2 1 46 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 116 (accept_3_2 1 92 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 116))))))))))))))))))))))))) (allB_succ' 26 91 116 (Eq.refl Bool.true) (allA_of_3_0 26 91 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 90 116 (Eq.refl Bool.true) (allA_succ_of_gcd 26 90 116 2 13 45
  58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 116
  (accept_3_2 25 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 116 2 12 45 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 116
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 116 2 11 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 90 116 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 90 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 116 2 10 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 116 (accept_3_2 19 90 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 116 2 9 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 90 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 90 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 116 2 8 45 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 116
  (Polychromatic418967fa.accept_11_4_2_6_1_389 15 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 90 116 2 7 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 90 116 (accept_3_2 13 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90
  116 2 6 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  90 116 (Polychromatic418967fa.accept_22_11_2_6_1_5439 11 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 116 2 5 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 90 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 90 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 116 2 4 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 116 (accept_3_2 7 90 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 116 2 3 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 90 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 90 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 116 2 2 45 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 116
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 116 2 1 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 116 (accept_3_2 1 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  116))))))))))))))))))))))))))) (allB_succ' 28 89 116 (Eq.refl Bool.true) (allA_succ_of_accept 27 89 116
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 89 116 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 89 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 116 (accept_3_2 25 89 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 89 116 (Polychromatic418967fa.accept_16_8_9_4_1_630 24 89 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 23
  89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 116 (accept_3_2 22 89
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 116 (Polychromatic418967fa.accept_6_3_5_2_1_12
  21 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 116
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 116 (accept_3_2 19 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 116 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 116 (Polychromatic418967fa.accept_13_4_11_12_1_1318 17 89 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 116 (accept_3_2 16 89 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 116
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 116 (accept_3_2 13 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 116 (Polychromatic418967fa.accept_15_12_14_11_1_4375 12 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 116 (Polychromatic418967fa.accept_16_11_9_4_1_5438 11 89 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 116 (accept_3_2 10 89 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 116
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 116 (accept_3_2 7 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  116 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 116 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 89 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 116 (accept_3_2 4 89 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 116 (accept_3_2 1 89 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 116)))))))))))))))))))))))))))) (allB_succ' 29 88 116 (Eq.refl
  Bool.true) (allA_of_3_0 29 88 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 87 116 (Eq.refl Bool.true)
  (allA_succ_of_gcd 29 87 116 29 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 28 87 116 (accept_3_2 28 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 116 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 116 (Polychromatic418967fa.accept_20_6_7_16_1_5437 26 87 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 116 (accept_3_2 25 87 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 116 (Polychromatic418967fa.accept_16_8_7_4_1_2217 24 87 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 116 (accept_3_2 22 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 116 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 116 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 87 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 116 (accept_3_2 19 87 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 116 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 87 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 116 (accept_3_2 16 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 116 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 116 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 87 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 116 (accept_3_2 13 87 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 116 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 87 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 116 (accept_3_2 10 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 116 (Polychromatic418967fa.accept_19_9_11_2_1_5436 9 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 87 116 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 87 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 116 (accept_3_2 7 87 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 116 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 87 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 116 (accept_3_2 4 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  116 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 116 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 87 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 116 (accept_3_2 1 87 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 116)))))))))))))))))))))))))))))) (allB_succ' 31 86 116 (Eq.refl Bool.true) (allA_succ_of_gcd
  30 86 116 2 15 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 86 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 86 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 116 2 14 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 27
  86 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 116 2 13 43 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 116 (accept_3_2 25
  86 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 116 2 12 43 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 116
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 86 116 2 11 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 86 116 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 86 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 116 2 10 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 116 (accept_3_2 19 86 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 116 2 9 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 86 116 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 86 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 116 2 8 43 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 116
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 116 2 7 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 116 (accept_3_2 13 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  116 2 6 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 116 2 5 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 116 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 86 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 116 2 4 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 116 (accept_3_2 7 86 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 116 2 3 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 116 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 86 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 116 2 2 43 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 116
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 116 2 1 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 116 (accept_3_2 1 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  116))))))))))))))))))))))))))))))) (allB_succ' 32 85 116 (Eq.refl Bool.true) (allA_of_3_0 32 85 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 84 116 (Eq.refl Bool.true) (allA_succ_of_gcd 32 84 116 4 8 21 29
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 116
  (accept_3_2 31 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 116 2 15 42 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 116
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 116 4 7 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 84 116 (Polychromatic418967fa.accept_26_1_6_12_1_5435 27 84 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 116 2 13 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 116 (accept_3_2 25 84 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 116 4 6 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 84 116 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 84 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 116 2 11 42 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 116
  (Polychromatic418967fa.accept_15_6_9_11_1_858 21 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 116 4 5 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 116 (accept_3_2 19 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84
  116 2 9 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  84 116 (Polychromatic418967fa.accept_15_2_9_11_1_1551 17 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 116 4 4 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 116 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 84 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 116 2 7 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 116 (accept_3_2 13 84 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 116 4 3 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 84 116 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 116 2 5 42 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 116
  (Polychromatic418967fa.accept_23_9_15_1_1_5434 9 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 116 4 2 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 116 (accept_3_2 7 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 116
  2 3 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84
  116 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 116 4 1 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 84 116 (Polychromatic418967fa.accept_18_3_12_8_1_5415 3 84 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 116 2 1 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 116 (accept_3_2 1 84 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 116))))))))))))))))))))))))))))))))) (allB_succ' 34 83 116 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 83 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 83 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 83 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 116 (accept_3_2 31 83 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 30
  83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 116
  (Polychromatic418967fa.accept_10_9_3_6_1_686 29 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 116 (accept_3_2 28 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 83 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 116 (accept_3_2 25 83 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 83 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 116
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 116 (accept_3_2 22 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 116 (Polychromatic418967fa.accept_13_7_5_12_1_1305 20 83 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 116 (accept_3_2 19 83 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 116 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 83 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 116
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 116 (accept_3_2 16 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 83 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 116 (accept_3_2 13 83 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 83 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 116
  (Polychromatic418967fa.accept_22_11_17_6_1_5433 11 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 116 (accept_3_2 10 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 116 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 83 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 116 (accept_3_2 7 83 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 116 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 83 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 116
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 116 (accept_3_2 4 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 83 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 116 (accept_3_2 1 83 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 116)))))))))))))))))))))))))))))))))) (allB_succ' 35 82 116 (Eq.refl Bool.true) (allA_of_3_0
  35 82 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 81 116 (Eq.refl Bool.true) (allA_succ_of_accept 35
  81 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 81 116 (accept_3_2 34 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 81 116 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 81 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 116 (Polychromatic418967fa.accept_10_2_1_6_1_634 32 81 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 116 (accept_3_2 31 81 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 116 (Polychromatic418967fa.accept_12_6_9_8_1_165
  30 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 116 (accept_3_2 28 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 116 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 116 (Polychromatic418967fa.accept_19_7_5_2_1_2842 26 81 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 116 (accept_3_2 25 81 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 116 (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 81 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 116 (accept_3_2 22 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 116 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 116 (Polychromatic418967fa.accept_15_5_6_11_1_854 20 81 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 116 (accept_3_2 19 81 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 116 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 81 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 116 (accept_3_2 16 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 116 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 116 (Polychromatic418967fa.accept_16_14_1_4_1_5432 14 81 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 116 (accept_3_2 13 81 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 116 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 81 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 116 (accept_3_2 10 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 116 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 116 (Polychromatic418967fa.accept_14_8_11_4_1_3438 8 81 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 116 (accept_3_2 7 81 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 116 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 81 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 116 (accept_3_2 4 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  116 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 81 116 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 81 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 116 (accept_3_2 1 81 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 81 116)))))))))))))))))))))))))))))))))))) (allB_succ' 37 80 116 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 80 116 4 9 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 80 116 (Polychromatic418967fa.accept_14_7_10_4_1_130 35 80 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 116 2 17 40 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 116 (Polychromatic418967fa.accept_19_14_4_2_1_2840
  33 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 116 4 8 20 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 116 (accept_3_2 31
  80 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 116 2 15 40 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 116
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 80 116 4 7 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 80 116 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 80 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 116 2 13 40 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 116 (accept_3_2 25 80 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 116 4 6 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 80 116 (Polychromatic418967fa.accept_13_10_2_12_1_1332 23 80 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 116 2 11 40 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 116
  (Polychromatic418967fa.accept_14_7_10_4_1_130 21 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 116 4 5 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 116 (accept_3_2 19 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  116 2 9 40 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 116 (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 116 4 4 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 116 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 80 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 116 2 7 40 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 116 (accept_3_2 13 80 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 116 4 3 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 80 116 (Polychromatic418967fa.accept_17_11_12_14_1_5431 11 80 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 116 2 5 40 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 116
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 116 4 2 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 116 (accept_3_2 7 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 116
  2 3 40 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  116 (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 80 116 4 1 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 80 116 (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 80 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 116 2 1 40 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 116 (accept_3_2 1 80 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 80 116))))))))))))))))))))))))))))))))))))) (allB_succ' 38 79 116 (Eq.refl Bool.true)
  (allA_of_3_0 38 79 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 78 116 (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 78 116 2 19 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 78 116 (accept_3_2 37 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78
  116 2 18 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  78 116 (Polychromatic418967fa.accept_17_1_10_14_1_1173 35 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 78 116 2 17 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 78 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 78 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 116 2 16 39 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 116 (accept_3_2 31 78 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 116 2 15 39 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 116
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 116 2 14 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 78 116 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 78 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 116 2 13 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 116 (accept_3_2 25 78 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 116 2 12 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 116 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 78 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 116 2 11 39 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 116
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 116 2 10 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 78 116 (accept_3_2 19 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78
  116 2 9 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  78 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 78 116 2 8 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 78 116 (Polychromatic418967fa.accept_12_3_6_8_1_969 15 78 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 116 2 7 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 116 (accept_3_2 13 78 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 116 2 6 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 78 116 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 78 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 116 2 5 39 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 116
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 116 2 4 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 116 (accept_3_2 7 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 116
  2 3 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78
  116 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 78 116 2 2 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 78 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 78 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 116 2 1 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 116 (accept_3_2 1 78 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 116))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 77 116 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 77 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 77 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 77 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 116 (accept_3_2 37 77 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 116 (Polychromatic418967fa.accept_15_6_2_11_1_325
  36 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 116
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 116 (accept_3_2 34 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 116 (Polychromatic418967fa.accept_18_14_5_8_1_1880 32 77 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 116 (accept_3_2 31 77 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 116 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 77 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 116
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 116 (accept_3_2 28 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 116 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 77 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 116 (accept_3_2 25 77 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 116 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 116
  (Polychromatic418967fa.accept_10_3_7_6_1_659 23 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 116 (accept_3_2 22 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 116 (accept_3_2 19 77 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 116 (Polychromatic418967fa.accept_19_18_1_2_1_5430 18 77 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 116
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 116 (accept_3_2 16 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 116 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 77 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 116 (accept_3_2 13 77 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 116 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 116
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 116 (accept_3_2 10 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 116 (Polychromatic418967fa.accept_16_8_13_4_1_3258 8 77 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 116 (accept_3_2 7 77 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 116 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 77 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 116
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 116 (accept_3_2 4 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 77 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 116 (accept_3_2 1 77 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 116)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 76 116 (Eq.refl Bool.true)
  (allA_of_3_0 41 76 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 75 116 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 75 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 116 (accept_3_2 40 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 116 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 75 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 116 (Polychromatic418967fa.accept_9_2_3_8_1_318 38
  75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 116 (accept_3_2 37 75
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 116
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 116 (accept_3_2 34 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 116 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 75 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 116 (Polychromatic418967fa.accept_9_5_3_8_1_316 32
  75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 116 (accept_3_2 31 75
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 116
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 116 (accept_3_2 28 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 116 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 75 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 116
  (Polychromatic418967fa.accept_21_5_12_11_1_5429 26 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 116 (accept_3_2 25 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 116 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 116 (accept_3_2 22 75 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 116 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 75 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 116
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 116 (accept_3_2 19 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 116 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 116 (accept_3_2 16 75 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 116 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 75 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 116
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 116 (accept_3_2 13 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 116 (Polychromatic418967fa.accept_16_12_11_4_1_1359 12 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 116 (accept_3_2 10 75 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 75 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 116
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 116 (accept_3_2 7 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  116 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 116 (accept_3_2 4 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 116 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 75 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 116 (accept_3_2 1 75 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 116)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 74
  116 (Eq.refl Bool.true) (allA_succ_of_gcd 42 74 116 2 21 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 74 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 74 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 116 2 20 37 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 116
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 116 2 19 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 74 116 (accept_3_2 37 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74
  116 2 18 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  74 116 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 74 116 2 17 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 74 116 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 74 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 116 2 16 37 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 116 (accept_3_2 31 74 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 116 2 15 37 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 116
  (Polychromatic418967fa.accept_12_5_2_8_1_172 29 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 74 116 2 14 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 74 116 (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 74 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 74 116 2 13 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 74 116 (accept_3_2 25 74 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74 116 2 12 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 74 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 74 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 116 2 11 37 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 116
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 116 2 10 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 74 116 (accept_3_2 19 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74
  116 2 9 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  74 116 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 74 116 2 8 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 74 116 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 74 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 116 2 7 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 116 (accept_3_2 13 74 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 116 2 6 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 74 116 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 74 116 2 5 37 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 74 116
  (Polychromatic418967fa.accept_19_9_17_2_1_5428 9 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 74 116 2 4 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 74 116 (accept_3_2 7 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 116
  2 3 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 74
  116 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 74 116 2 2 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 74 116 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 74 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 116 2 1 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 116 (accept_3_2 1 74 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 116))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 73 116 (Eq.refl Bool.true)
  (allA_of_3_0 44 73 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 72 116 (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 72 116 4 11 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 116 (accept_3_2 43 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72
  116 2 21 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  72 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 72 116 4 10 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 72 116 (Polychromatic418967fa.accept_16_7_8_4_1_689 39 72 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 116 2 19 36 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 116 (accept_3_2 37 72 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 116 4 9 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 116 (Polychromatic418967fa.accept_16_3_8_4_1_3279
  35 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 116 2 17 36 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 116
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 116 4 8 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 116 (accept_3_2 31 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72
  116 2 15 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  72 116 (Polychromatic418967fa.accept_15_14_12_11_1_1572 29 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 72 116 4 7 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 72 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 116 2 13 36 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 116 (accept_3_2 25 72 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 116 4 6 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 116 (Polychromatic418967fa.accept_13_10_7_12_1_2782 23 72
  116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 116 2 11 36 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 116
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 116 4 5 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 116 (accept_3_2 19 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  116 2 9 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 116 (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 116 4 4 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 116 (Polychromatic418967fa.accept_16_15_8_4_1_1355 15 72 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 116 2 7 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 116 (accept_3_2 13 72 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 116 4 3 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 72 116 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 72 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 116 2 5 36 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 116
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 116 4 2 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 116 (accept_3_2 7 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 116
  2 3 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  116 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 72 116 4 1 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 72 116 (Polychromatic418967fa.accept_16_3_8_4_1_3279 3 72 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 116 2 1 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 116 (accept_3_2 1 72 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 116))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 71 116 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 71 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 71 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 116 (Polychromatic418967fa.accept_13_5_6_12_1_2750 44 71
  116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 116 (accept_3_2 43 71 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 116 (Polychromatic418967fa.accept_10_2_1_6_1_634
  42 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 116
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 41 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 116 (accept_3_2 40 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 116 (accept_3_2 37 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 116 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 71 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 116
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 116 (accept_3_2 34 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 116 (Polychromatic418967fa.accept_10_2_1_6_1_634 32 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 116 (accept_3_2 31 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 116 (Polychromatic418967fa.accept_16_14_7_4_1_3243 30 71 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 116
  (Polychromatic418967fa.accept_16_13_7_4_1_3248 29 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 116 (accept_3_2 28 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 116 (accept_3_2 25 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 71 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 116
  (Polychromatic418967fa.accept_11_1_5_6_1_397 23 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 116 (accept_3_2 22 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 116 (Polychromatic418967fa.accept_13_7_6_12_1_2027 20 71 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 116 (accept_3_2 19 71 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 116 (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 71
  116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 116
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 116 (accept_3_2 16 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 116 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 116 (accept_3_2 13 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 71 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 116
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 116 (accept_3_2 10 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 116 (Polychromatic418967fa.accept_16_8_7_4_1_2217 8 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 116 (accept_3_2 7 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 116 (Polychromatic418967fa.accept_17_6_3_14_1_2078 6 71 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 116
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 116 (accept_3_2 4 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 116 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 71 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 116 (accept_3_2 1 71 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 116)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 70 116 (Eq.refl Bool.true)
  (allA_of_3_0 47 70 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 69 116 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 69 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 116 (accept_3_2 46 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 69 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 69 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 44
  69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 116 (accept_3_2 43 69
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 116
  (Polychromatic418967fa.accept_11_9_3_6_1_797 42 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 69 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 116 (accept_3_2 40 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 69 116 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 69 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 38
  69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 116 (accept_3_2 37 69
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 116
  (Polychromatic418967fa.accept_15_6_9_11_1_858 36 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 69 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 116 (accept_3_2 34 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 69 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 69 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 116 (Polychromatic418967fa.accept_9_5_6_8_1_101 32
  69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 116 (accept_3_2 31 69
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 116 (Polychromatic418967fa.accept_7_2_6_4_1_29
  30 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 116 (accept_3_2 28 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  69 116 (Polychromatic418967fa.accept_17_10_1_14_1_489 27 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 69 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 69 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 116 (accept_3_2 25 69 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 116 (accept_3_2 22 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  69 116 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 69 116 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 69 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 116 (accept_3_2 19 69 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 116 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 69 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 116 (accept_3_2 16 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  69 116 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 116 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 69 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 116 (accept_3_2 13 69 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 116 (accept_3_2 10 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  69 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 69 116 (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 69 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 116 (accept_3_2 7 69 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 116 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 69 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 116 (accept_3_2 4 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69
  116 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 116 (accept_3_2 1 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 69 116)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 68 116 (Eq.refl Bool.true)
  (allA_succ_of_gcd 48 68 116 4 12 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 68 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 68 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 68 116 2 23 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 68 116 (Polychromatic418967fa.accept_22_1_2_6_1_5427
  45 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 116 4 11 17 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 116 (accept_3_2 43
  68 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 116 2 21 34 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 116
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 68 116 4 10 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 68 116 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 68 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 116 2 19 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 116 (accept_3_2 37 68 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 116 4 9 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 68 116 (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 68 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 116 2 17 34 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 116
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 116 4 8 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 116 (accept_3_2 31 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  116 2 15 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  68 116 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 116 4 7 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 68 116 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 68 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 116 2 13 34 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 116 (accept_3_2 25 68 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 116 4 6 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 68 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 116 2 11 34 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 116
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 116 4 5 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 116 (accept_3_2 19 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  116 2 9 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 116 (Polychromatic418967fa.accept_13_4_3_12_1_2066 17 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 116 4 4 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 116 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 68 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 116 2 7 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 116 (accept_3_2 13 68 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 116 4 3 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 68 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 68 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 116 2 5 34 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 116
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 116 4 2 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 116 (accept_3_2 7 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 116
  2 3 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  116 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 68 116 4 1 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 68 116 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 68 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 116 2 1 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 116 (accept_3_2 1 68 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 68 116))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 67 116 (Eq.refl
  Bool.true) (allA_of_3_0 50 67 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 66 116 (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 66 116 2 25 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 66 116 (accept_3_2 49 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66
  116 2 24 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  66 116 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 66 116 2 23 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 66 116 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 66 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 116 2 22 33 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 116 (accept_3_2 43 66 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 116 2 21 33 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 116
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 66 116 2 20 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 66 116 (Polychromatic418967fa.accept_12_3_6_8_1_969 39 66 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 116 2 19 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 116 (accept_3_2 37 66 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 116 2 18 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 116 (Polychromatic418967fa.accept_14_7_10_4_1_130 35 66 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 116 2 17 33 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 116
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 116 2 16 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 66 116 (accept_3_2 31 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66
  116 2 15 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  66 116 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 66 116 2 14 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 66 116 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 66 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 116 2 13 33 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 116 (accept_3_2 25 66 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 116 2 12 33 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 116
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 116 2 11 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 66 116 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 66 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 116 2 10 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 116 (accept_3_2 19 66 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 116 2 9 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 66 116 (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 66 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 116 2 8 33 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 116
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 66 116 2 7 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 66 116 (accept_3_2 13 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66
  116 2 6 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  66 116 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 66 116 2 5 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 66 116 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 66 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 116 2 4 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 116 (accept_3_2 7 66 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 116 2 3 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 66 116 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 66 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 116 2 2 33 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 116
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 66 116 2 1 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 116 (accept_3_2 1 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  116))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 65 116 (Eq.refl Bool.true) (allA_succ_of_accept
  51 65 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 116 (accept_3_2 49 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 65 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 116
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 116 (accept_3_2 46 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 116 (Polychromatic418967fa.accept_10_4_5_6_1_651 44 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 116 (accept_3_2 43 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 116 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 65 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 116
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 116 (accept_3_2 40 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 116 (Polychromatic418967fa.accept_11_5_10_6_1_793 38 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 116 (accept_3_2 37 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 116 (Polychromatic418967fa.accept_15_6_5_11_1_2378 36 65 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 116
  (Polychromatic418967fa.accept_16_3_1_4_1_5426 35 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 116 (accept_3_2 34 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 116 (accept_3_2 31 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 116 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 65 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 116
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 116 (accept_3_2 28 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 116 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 116 (accept_3_2 25 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 116 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 65 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 116
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 116 (accept_3_2 22 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 116 (accept_3_2 19 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 116 (Polychromatic418967fa.accept_20_18_5_16_1_5425 18 65 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 116
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 116 (accept_3_2 16 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 116 (accept_3_2 13 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 116 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 65 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 116
  (Polychromatic418967fa.accept_10_1_5_6_1_649 11 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 116 (accept_3_2 10 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 116 (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 116 (accept_3_2 7 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 65 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 116
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 116 (accept_3_2 4 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 116 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 65 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 116 (accept_3_2 1 65 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 116)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 64 116 (Eq.refl
  Bool.true) (allA_of_3_0 53 64 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 63 116 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 63 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 116 (accept_3_2 52 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 63 116 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 63 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 116 (Polychromatic418967fa.accept_19_12_6_2_1_5424
  50 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 116 (accept_3_2 49
  63 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 63 116
  (Polychromatic418967fa.accept_10_8_3_6_1_685 48 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 63 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 116 (accept_3_2 46 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 63 116 (Polychromatic418967fa.accept_14_3_7_4_1_118 45 63 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 116 (Polychromatic418967fa.accept_15_14_3_11_1_850
  44 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 116 (accept_3_2 43
  63 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 63 116
  (Polychromatic418967fa.accept_12_6_3_8_1_512 42 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 63 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 116 (accept_3_2 40 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 63 116 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 63 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 116 (Polychromatic418967fa.accept_10_8_3_6_1_685
  38 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 116 (accept_3_2 37
  63 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 116
  (Polychromatic418967fa.accept_11_3_8_6_1_788 36 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 63 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 116 (accept_3_2 34 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 63 116 (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 63 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 116
  (Polychromatic418967fa.accept_17_15_12_14_1_2087 32 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 63 116 (accept_3_2 31 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 63 116 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 63 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 116 (accept_3_2 28 63 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 116 (Polychromatic418967fa.accept_8_3_7_4_1_42 27
  63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 116
  (Polychromatic418967fa.accept_17_9_12_14_1_5423 26 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 116 (accept_3_2 25 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 116 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 116 (accept_3_2 22 63 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 116 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 63 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 116
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 20 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 116 (accept_3_2 19 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 116 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 116 (accept_3_2 16 63 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 116 (Polychromatic418967fa.accept_17_15_12_14_1_2087 15 63 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 116
  (Polychromatic418967fa.accept_11_3_8_6_1_788 14 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 116 (accept_3_2 13 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 116 (Polychromatic418967fa.accept_16_12_15_4_1_5422 12 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 116 (accept_3_2 10 63 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 116 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 63 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 116
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 116 (accept_3_2 7 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  116 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 116 (accept_3_2 4 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 116 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 116 (Polychromatic418967fa.accept_22_2_19_6_1_5421
  2 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 116 (accept_3_2 1 63
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 116))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 62 116 (Eq.refl Bool.true) (allA_succ_of_gcd 54 62 116 2 27 31 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 116
  (Polychromatic418967fa.accept_12_5_2_8_1_172 53 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 62 116 2 26 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 62 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 62 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 62 116 2 25 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 62 116 (accept_3_2 49 62 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62 116 2 24 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 62 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 62 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 116 2 23 31 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 116
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 116 2 22 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 62 116 (accept_3_2 43 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62
  116 2 21 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  62 116 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 62 116 2 20 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 62 116 (Polychromatic418967fa.accept_15_9_2_11_1_2391 39 62 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 116 2 19 31 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 116 (accept_3_2 37 62 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 116 2 18 31 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 116
  (Polychromatic418967fa.accept_12_11_2_8_1_511 35 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 62 116 2 17 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 62 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 62 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 62 116 2 16 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 62 116 (accept_3_2 31 62 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62 116 2 15 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 62 116 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 62 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 116 2 14 31 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 116
  (Polychromatic418967fa.accept_19_8_5_2_1_4105 27 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 116 2 13 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 62 116 (accept_3_2 25 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62
  116 2 12 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  62 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 62 116 2 11 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 62 116 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 62 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 116 2 10 31 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 116 (accept_3_2 19 62 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 116 2 9 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 62 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 17
  62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 116 2 8 31 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 116
  (Polychromatic418967fa.accept_13_2_10_12_1_757 15 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 116 2 7 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 116 (accept_3_2 13 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  116 2 6 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 116 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 116 2 5 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 62 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 116 2 4 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 116 (accept_3_2 7 62 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 116 2 3 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 62 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 116 2 2 31 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 116
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 116 2 1 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 116 (accept_3_2 1 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  116))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 61 116 (Eq.refl Bool.true) (allA_of_3_0 56
  61 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 60 116 (Eq.refl Bool.true) (allA_succ_of_gcd 56 60 116
  4 14 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60
  116 (accept_3_2 55 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 116 2 27 30 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 116
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 53 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 60 116 4 13 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 60 116 (Polychromatic418967fa.accept_16_3_12_4_1_170 51 60 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 116 2 25 30 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 116 (accept_3_2 49 60 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 116 4 12 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 116 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 60 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 116 2 23 30 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 116
  (Polychromatic418967fa.accept_11_1_5_6_1_397 45 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 60 116 4 11 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 60 116 (accept_3_2 43 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60
  116 2 21 30 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  60 116 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 60 116 4 10 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 60 116 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 60 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 116 2 19 30 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 116 (accept_3_2 37 60 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 116 4 9 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 116 (Polychromatic418967fa.accept_13_9_8_12_1_2031
  35 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 116 2 17 30 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 116
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 116 4 8 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 116 (accept_3_2 31 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  116 2 15 30 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 116 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 116 4 7 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 116 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 60 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 116 2 13 30 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 116 (accept_3_2 25 60 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 116 4 6 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 116 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 60 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 116 2 11 30 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 116
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 116 4 5 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 116 (accept_3_2 19 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60
  116 2 9 30 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  60 116 (Polychromatic418967fa.accept_13_4_8_12_1_3526 17 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 116 4 4 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 116 (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 60 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 116 2 7 30 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 116 (accept_3_2 13 60 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 116 4 3 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 116 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 116 2 5 30 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 116
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 116 4 2 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 116 (accept_3_2 7 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 116
  2 3 30 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60
  116 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 60 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 116 4 1 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 60 116 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 60 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 116 2 1 30 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 116 (accept_3_2 1 60 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 116))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 59 116 (Eq.refl
  Bool.true) (allA_succ_of_accept 57 59 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 59 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 59 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 56
  59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 116 (accept_3_2 55 59
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 116
  (Polychromatic418967fa.accept_16_6_11_4_1_635 54 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 59 116 (Polychromatic418967fa.accept_10_3_9_6_1_94 53 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 116 (accept_3_2 52 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 59 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 116 (Polychromatic418967fa.accept_7_1_3_4_1_128 50
  59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 116 (accept_3_2 49 59
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 116
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 59 116 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 116 (accept_3_2 46 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 59 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 116 (Polychromatic418967fa.accept_13_5_7_12_1_2757
  44 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 116 (accept_3_2 43
  59 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 116
  (Polychromatic418967fa.accept_9_6_5_8_1_598 42 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 59 116 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 116 (accept_3_2 40 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 59 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 38
  59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 116 (accept_3_2 37 59
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 116
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 59 116 (Polychromatic418967fa.accept_10_5_9_6_1_697 35 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 116 (accept_3_2 34 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 59 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 116 (Polychromatic418967fa.accept_13_6_7_12_1_3504
  32 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 116 (accept_3_2 31
  59 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 116
  (Polychromatic418967fa.accept_9_3_5_8_1_99 30 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 59 116 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 116 (accept_3_2 28 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 59 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 116 (Polychromatic418967fa.accept_12_2_11_8_1_504
  26 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 116 (accept_3_2 25
  59 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 116
  (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 59 116 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 116 (accept_3_2 22 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 59 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 116 (Polychromatic418967fa.accept_7_6_3_4_1_294 20
  59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 116 (accept_3_2 19 59
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 116
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 59 116 (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 116 (accept_3_2 16 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 59 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 116 (Polychromatic418967fa.accept_12_2_11_8_1_504
  14 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 116 (accept_3_2 13
  59 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 116
  (Polychromatic418967fa.accept_9_3_5_8_1_99 12 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 59 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 116 (accept_3_2 10 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 59 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 116 (Polychromatic418967fa.accept_7_1_3_4_1_128 8
  59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 116 (accept_3_2 7 59 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 116 (Polychromatic418967fa.accept_7_6_3_4_1_294 6
  59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 116
  (Polychromatic418967fa.accept_10_5_9_6_1_697 5 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 116 (accept_3_2 4 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 116 (accept_3_2 1 59 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 116)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 116 (allA_of_3_0
  58 58 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 116 (allA_succ_of_accept 56 57 116
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 116 (accept_3_2 55 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 116 (accept_3_2 52 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 116 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 57 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 116
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 116 (accept_3_2 49 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 116 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 116 (accept_3_2 46 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 57 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 116
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 44 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 57 116 (accept_3_2 43 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 116 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 57 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 116 (accept_3_2 40 57 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 116 (Polychromatic418967fa.accept_14_11_1_4_1_4445
  39 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 116
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 116 (accept_3_2 37 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 116 (Polychromatic418967fa.accept_22_14_13_6_1_5420 36 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 116 (accept_3_2 34 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 57 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 116
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 116 (accept_3_2 31 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 116 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 116 (accept_3_2 28 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 116 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 57 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 116
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 116 (accept_3_2 25 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 116 (accept_3_2 22 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 116 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 116
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 116 (accept_3_2 19 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 116 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 116 (accept_3_2 16 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 116 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 116
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 116 (accept_3_2 13 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 116 (accept_3_2 10 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 116 (Polychromatic418967fa.accept_18_9_3_8_1_5419 9 57 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 116
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 8 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 116 (accept_3_2 7 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  116 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 116 (accept_3_2 4 57 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 57 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 116 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  57 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 116 (accept_3_2 1 57 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 116)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 116 (allA_succ_of_accept 55 56 116 (accept_3_2 55 56 116 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 116 2 27 28 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 116 (Polychromatic418967fa.accept_16_5_8_4_1_5418 53 56 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 116 4 13 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 116 (Polychromatic418967fa.accept_9_6_2_8_1_592 51
  56 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 116 2 25 28 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 116 (accept_3_2 49
  56 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 116 4 12 14 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 116
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 47 56 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 116 2 23 28 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 116 (Polychromatic418967fa.accept_16_13_8_4_1_3250 45 56 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 116 4 11 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 116 (accept_3_2 43 56 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 116 2 21 28 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 116 4 10 14 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 116
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 56 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 116 2 19 28 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 116 (accept_3_2 37 56 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  116 4 9 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  56 116 (Polychromatic418967fa.accept_16_3_8_4_1_3279 35 56 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 56 116 2 17 28 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 116 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 56 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 116 4 8 14 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 116 (accept_3_2 31 56 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 116 2 15 28 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 116 (Polychromatic418967fa.accept_11_7_1_6_1_1281
  29 56 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 116 4 7 14 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 116
  (Polychromatic418967fa.accept_11_5_1_6_1_774 27 56 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 56 116 2 13 28 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 56 116 (accept_3_2 25 56 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56
  116 4 6 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  56 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 56 116 2 11 28 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 56 116 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 56 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 116 4 5 14 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 116 (accept_3_2 19 56 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 116 2 9 28 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 56 116 (Polychromatic418967fa.accept_16_1_8_4_1_4334 17 56 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 116 4 4 14 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 116
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 56 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 56 116 2 7 28 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 56 116 (accept_3_2 13 56 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56
  116 4 3 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  56 116 (Polychromatic418967fa.accept_13_11_4_12_1_3585 11 56 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 56 116 2 5 28 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 116 (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 56 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 116 4 2 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 116 (accept_3_2 7 56 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 116 2 3 28 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 56 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 116 4 1 14 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 116
  (Polychromatic418967fa.accept_9_3_2_8_1_108 3 56 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 56 116 2 1 28 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 56 116 (accept_3_2 1 56 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  116)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 116 (allA_of_3_0 55 55 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 54 116 (allA_succ_of_accept 53 54 116
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 53 54 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 116 2 26 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 54 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 116 2 25 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 116 (accept_3_2 49 54 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 116 2 24 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 116 (Polychromatic418967fa.accept_15_2_9_11_1_1551 47 54 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 116 2 23 27 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 116
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 54 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 116 2 22 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 116 (accept_3_2 43 54 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54
  116 2 21 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  54 116 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 54 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 54 116 2 20 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 54 116 (Polychromatic418967fa.accept_12_3_6_8_1_969 39 54 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 116 2 19 27 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 116 (accept_3_2 37 54 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 116 2 18 27 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 116
  (Polychromatic418967fa.accept_10_5_4_6_1_319 35 54 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 116 2 17 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 54 116 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 116 2 16 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 116 (accept_3_2 31 54 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 116 2 15 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 116 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 54 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 116 2 14 27 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 116
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 54 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 116 2 13 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 116 (accept_3_2 25 54 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54
  116 2 12 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  54 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 54 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 54 116 2 11 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 54 116 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 116 2 10 27 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 116 (accept_3_2 19 54 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 116 2 9 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 116 (Polychromatic418967fa.accept_13_4_2_12_1_2800
  17 54 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 116 2 8 27 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 116
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 54 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 54 116 2 7 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 116 (accept_3_2 13 54 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54
  116 2 6 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  54 116 (Polychromatic418967fa.accept_16_11_6_4_1_2228 11 54 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 116 2 5 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 54 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 54 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 116 2 4 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 116 (accept_3_2 7 54 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 116 2 3 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 54 116 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 54 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 116 2 2 27 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 116
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 54 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 116 2 1 27 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 116 (accept_3_2 1 54 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  116)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 116 (allA_succ_of_accept 52 53 116 (accept_3_2
  52 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 116
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 116 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 53 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 116 (accept_3_2 49 53 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 116 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 53 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 116 (Polychromatic418967fa.accept_10_7_3_6_1_644
  47 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 116 (accept_3_2 46
  53 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 116
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 116 (Polychromatic418967fa.accept_13_5_1_12_1_740 44 53 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 116 (accept_3_2 43 53 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 116 (Polychromatic418967fa.accept_15_12_8_11_1_4383 42 53 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 116
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 116 (accept_3_2 40 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 116 (Polychromatic418967fa.accept_10_8_3_6_1_685 38 53 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 116 (accept_3_2 37 53 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 116 (Polychromatic418967fa.accept_11_3_9_6_1_105 36 53 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 116
  (Polychromatic418967fa.accept_14_7_11_4_1_3455 35 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 116 (accept_3_2 34 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 116 (Polychromatic418967fa.accept_19_13_15_2_1_4126 32 53 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 116 (accept_3_2 31 53 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 116 (Polychromatic418967fa.accept_19_11_15_2_1_4096 30 53
  116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 116
  (Polychromatic418967fa.accept_10_9_3_6_1_686 29 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 116 (accept_3_2 28 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 116 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 53 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 116 (accept_3_2 25 53 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 116 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 53 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 116
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 23 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 116 (accept_3_2 22 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 116 (Polychromatic418967fa.accept_15_5_8_11_1_2350 20 53 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 116 (accept_3_2 19 53 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 116 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 53 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 116
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 116 (accept_3_2 16 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 116 (Polychromatic418967fa.accept_11_3_9_6_1_105 14 53 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 116 (accept_3_2 13 53 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 116 (Polychromatic418967fa.accept_15_12_8_11_1_4383 12 53 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 116
  (Polychromatic418967fa.accept_13_11_1_12_1_742 11 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 116 (accept_3_2 10 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 116 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 53 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 116 (accept_3_2 7 53 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 116 (Polychromatic418967fa.accept_16_6_5_4_1_4330 6 53 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 116
  (Polychromatic418967fa.accept_13_5_1_12_1_740 5 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 116 (accept_3_2 4 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 116 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 53 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 116 (accept_3_2 1 53 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 116))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 116 (allA_of_3_0 52 52
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 116 (allA_succ_of_accept 50 51 116
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 116 (accept_3_2 49 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 116 (accept_3_2 46 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 116 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 51 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 116
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 44 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 116 (accept_3_2 43 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 116 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 116 (accept_3_2 40 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 116 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 51 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 116
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 116 (accept_3_2 37 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 116 (Polychromatic418967fa.accept_21_15_9_11_1_5417 36 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 116 (accept_3_2 34 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 116 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 51 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 116
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 116 (accept_3_2 31 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 116 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 116 (accept_3_2 28 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 116
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 116 (accept_3_2 25 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 116 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 116 (accept_3_2 22 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 116 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 116
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 116 (accept_3_2 19 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 116 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 116 (accept_3_2 16 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 116 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 51 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 116
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 116 (accept_3_2 13 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 116 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 116 (accept_3_2 10 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 116 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 51 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 116
  (Polychromatic418967fa.accept_16_8_3_4_1_3233 8 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 116 (accept_3_2 7 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  116 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 116 (accept_3_2 4 51 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 116 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 51 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 116 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  51 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 116 (accept_3_2 1 51 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 116)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 116 (allA_succ_of_accept 49 50 116 (accept_3_2 49 50 116 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 116 2 24 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 50 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 50 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 116 2 23 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 50 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 45
  50 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 116 2 22 25 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 116 (accept_3_2 43
  50 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 116 2 21 25 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 116
  (Polychromatic418967fa.accept_12_5_2_8_1_172 41 50 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 116 2 20 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 116 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 50 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 116 2 19 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 116 (accept_3_2 37 50 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 116 2 18 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 116 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 50 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 116 2 17 25 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 116
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 50 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 116 2 16 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 50 116 (accept_3_2 31 50 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50
  116 2 15 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  50 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 50 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 50 116 2 14 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 50 116 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 50 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 116 2 13 25 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 116 (accept_3_2 25 50 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 116 2 12 25 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 116
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 50 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 116 2 11 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 116 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 50 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 116 2 10 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 116 (accept_3_2 19 50 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 116 2 9 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 50 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 50 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 116 2 8 25 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 116
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 50 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 50 116 2 7 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 50 116 (accept_3_2 13 50 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50
  116 2 6 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  50 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 50 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 116 2 5 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 50 116 (Polychromatic418967fa.accept_15_9_5_11_1_5416 9 50 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 116 2 4 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 116 (accept_3_2 7 50 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 116 2 3 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 50 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 50 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 116 2 2 25 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 116
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 50 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 116 2 1 25 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 116 (accept_3_2 1 50 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  116)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 116 (allA_of_3_0 49 49 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 116 (allA_succ_of_accept 47 48 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 47
  48 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 116 2 23 24 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 116
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 48 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 116 4 11 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 116 (accept_3_2 43 48 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48
  116 2 21 24 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  48 116 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 48 116 4 10 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 48 116 (Polychromatic418967fa.accept_18_3_12_8_1_5415 39 48 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 116 2 19 24 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 116 (accept_3_2 37 48 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 116 4 9 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 116 (Polychromatic418967fa.accept_11_2_4_6_1_2412
  35 48 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 116 2 17 24 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 116
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 116 4 8 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 116 (accept_3_2 31 48 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48
  116 2 15 24 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  48 116 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 48 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 116 4 7 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 116 (Polychromatic418967fa.accept_19_8_10_2_1_5414 27 48 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 116 2 13 24 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 116 (accept_3_2 25 48 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 116 4 6 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 48 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 116 2 11 24 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 116
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 48 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 116 4 5 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 116 (accept_3_2 19 48 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48
  116 2 9 24 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  48 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 48 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 116 4 4 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 116 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 48 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 116 2 7 24 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 116 (accept_3_2 13 48 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 116 4 3 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 48 116 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 48 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 116 2 5 24 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 116
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 116 4 2 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 116 (accept_3_2 7 48 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 116
  2 3 24 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48
  116 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 48 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 116 4 1 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 48 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 116 2 1 24 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 116 (accept_3_2 1 48 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 116)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 116 (allA_succ_of_accept 46
  47 116 (accept_3_2 46 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 116
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 47 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 116 (accept_3_2 43 47 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 116 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 47 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 116 (Polychromatic418967fa.accept_7_6_5_4_1_297 41
  47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 116 (accept_3_2 40 47
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 116 (Polychromatic418967fa.accept_6_3_5_2_1_12
  39 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 116
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 116 (accept_3_2 37 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 116 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 116 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 47 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 116 (accept_3_2 34 47 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 116
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 116 (accept_3_2 31 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 116 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 47 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 116 (accept_3_2 28 47 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 116
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 116 (accept_3_2 25 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 116 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 47 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 116 (accept_3_2 22 47 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 116
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 116 (accept_3_2 19 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 116 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 116 (Polychromatic418967fa.accept_13_4_8_12_1_3526 17 47 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 116 (accept_3_2 16 47 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 116
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 116 (accept_3_2 13 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 116 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 116 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 47 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 116 (accept_3_2 10 47 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 116
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 116 (accept_3_2 7 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  116 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 47 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 116 (accept_3_2 4 47 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  47 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 116 (accept_3_2 1 47 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 116))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  116 (allA_of_3_0 46 46 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 116 (allA_succ_of_accept 44 45 116
  (Polychromatic418967fa.accept_10_4_5_6_1_651 44 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 116 (accept_3_2 43 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 116 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 116 (accept_3_2 40 45 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 116 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 45 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 116
  (Polychromatic418967fa.accept_11_5_1_6_1_774 38 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 116 (accept_3_2 37 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 116 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 45 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 116 (accept_3_2 34 45 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 116 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 45 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 116
  (Polychromatic418967fa.accept_19_13_7_2_1_5413 32 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 116 (accept_3_2 31 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 116 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 116 (accept_3_2 28 45 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 116 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 45 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 116
  (Polychromatic418967fa.accept_27_26_18_8_1_5412 26 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 116 (accept_3_2 25 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 116 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 116 (accept_3_2 22 45 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 116 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 45 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 116
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 116 (accept_3_2 19 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 116 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 116 (accept_3_2 16 45 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 116 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 45 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 116
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 116 (accept_3_2 13 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 116 (Polychromatic418967fa.accept_16_12_13_4_1_3198 12 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 116 (accept_3_2 10 45 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 116 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 45 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 116
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 116 (accept_3_2 7 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  116 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 116 (accept_3_2 4 45 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 116 (Polychromatic418967fa.accept_17_3_11_14_1_2071 3 45 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 116 (Polychromatic418967fa.accept_13_2_6_12_1_1334
  2 45 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 116 (accept_3_2 1 45
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 116))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  44 116 (allA_succ_of_accept 43 44 116 (accept_3_2 43 44 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  42 44 116 2 21 22 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 44 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 44 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 116 4 10 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 116 (Polychromatic418967fa.accept_16_7_12_4_1_1347
  39 44 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 116 2 19 22 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 116 (accept_3_2 37
  44 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 116 4 9 11 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 116
  (Polychromatic418967fa.accept_10_5_4_6_1_319 35 44 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 44 116 2 17 22 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 44 116 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 44 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 116 4 8 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 116 (accept_3_2 31 44 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 44 116 2 15 22 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 44 116 (Polychromatic418967fa.accept_16_13_12_4_1_4323 29 44 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 116 4 7 11 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 116
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 44 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 116 2 13 22 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 44 116 (accept_3_2 25 44 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44
  116 4 6 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  44 116 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 44 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 44 116 2 11 22 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 44 116 (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 44 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 116 4 5 11 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 116 (accept_3_2 19 44 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 116 2 9 22 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 116 (Polychromatic418967fa.accept_13_4_5_12_1_751 17 44 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 116 4 4 11 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 116
  (Polychromatic418967fa.accept_10_5_4_6_1_319 15 44 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 116 2 7 22 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 116 (accept_3_2 13 44 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44
  116 4 3 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  44 116 (Polychromatic418967fa.accept_16_11_12_4_1_3195 11 44 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 116 2 5 22 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 44 116 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 44 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 116 4 2 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 116 (accept_3_2 7 44 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 116 2 3 22 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 44 116 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 44 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 116 4 1 11 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 116
  (Polychromatic418967fa.accept_15_3_14_11_1_1579 3 44 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 116 2 1 22 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 116 (accept_3_2 1 44 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  116)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 116 (allA_of_3_0 43 43 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 42 116 (allA_succ_of_accept 41 42 116 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 42 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 116 2 20 21 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 116
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 42 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 116 2 19 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 116 (accept_3_2 37 42 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42
  116 2 18 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  42 116 (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 42 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 42 116 2 17 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 42 116 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 116 2 16 21 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 116 (accept_3_2 31 42 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 116 2 15 21 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 116
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 42 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 116 2 14 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 42 116 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 42 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 116 2 13 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 116 (accept_3_2 25 42 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 116 2 12 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 116 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 42 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 116 2 11 21 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 116
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 42 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 116 2 10 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 116 (accept_3_2 19 42 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42
  116 2 9 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  42 116 (Polychromatic418967fa.accept_13_4_3_12_1_2066 17 42 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 116 2 8 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 116 (Polychromatic418967fa.accept_12_3_6_8_1_969 15 42 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 116 2 7 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 116 (accept_3_2 13 42 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 116 2 6 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 42 116 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 42 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 116 2 5 21 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 116
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 116 2 4 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 116 (accept_3_2 7 42 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 116
  2 3 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42
  116 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 42 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 42 116 2 2 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 42 116 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 42 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 116 2 1 21 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 116 (accept_3_2 1 42 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 116)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 116 (allA_succ_of_accept 40 41
  116 (accept_3_2 40 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 116
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 41 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 116 (accept_3_2 37 41 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 116 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 41 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 116 (Polychromatic418967fa.accept_10_5_1_6_1_672
  35 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 116 (accept_3_2 34
  41 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 116
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 116 (Polychromatic418967fa.accept_10_2_1_6_1_634 32 41 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 116 (accept_3_2 31 41 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 41 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 116 (Polychromatic418967fa.accept_8_5_1_4_1_628 29
  41 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 116 (accept_3_2 28 41
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 116 (Polychromatic418967fa.accept_6_3_5_2_1_12
  27 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 116
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 116 (accept_3_2 25 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 41 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 116 (accept_3_2 22 41 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 116
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 116 (accept_3_2 19 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 116 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 41 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 116 (accept_3_2 16 41 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 116
  (Polychromatic418967fa.accept_11_3_8_6_1_788 14 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 116 (accept_3_2 13 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 41 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 116 (accept_3_2 10 41 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 116
  (Polychromatic418967fa.accept_16_8_9_4_1_630 8 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 116 (accept_3_2 7 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  116 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 41 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 41 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 116 (accept_3_2 4 41 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 41
  116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 116 (accept_3_2 1 41 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 116))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 116
  (allA_of_3_0 40 40 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 116 (allA_succ_of_accept 38 39 116
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 116 (accept_3_2 37 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 116 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 116 (accept_3_2 34 39 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 116 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 39 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 116
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 116 (accept_3_2 31 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 116 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 116 (accept_3_2 28 39 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 116 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 39 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 116
  (Polychromatic418967fa.accept_17_9_5_14_1_4277 26 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 116 (accept_3_2 25 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 116 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 116 (accept_3_2 22 39 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 116 (Polychromatic418967fa.accept_14_7_11_4_1_3455 21 39 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 116
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 116 (accept_3_2 19 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 116 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 116 (accept_3_2 16 39 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 116 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 39 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 116
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 116 (accept_3_2 13 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 116 (Polychromatic418967fa.accept_16_12_7_4_1_687 12 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 116 (accept_3_2 10 39 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 116 (Polychromatic418967fa.accept_17_9_5_14_1_4277 9 39 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 116
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 8 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 116 (accept_3_2 7 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  116 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 39 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 116 (accept_3_2 4 39 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 116 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 39 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 116 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  39 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 116 (accept_3_2 1 39 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 116))))))))))))))))))))))))))))))))))))))) (allB_succ 38 116
  (allA_succ_of_accept 37 38 116 (accept_3_2 37 38 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  116 2 18 19 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 116 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 38 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 116 2 17 19 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 116 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 38 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 116 2 16 19 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 116 (accept_3_2 31 38 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 116 2 15 19 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 116
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 38 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 116 2 14 19 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 116 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 38 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 116 2 13 19 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 116 (accept_3_2 25 38 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 116 2 12 19 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 38 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 116 2 11 19 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 116
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 38 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 116 2 10 19 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 116 (accept_3_2 19 38 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  116 2 9 19 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 116 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 38 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 116 2 8 19 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 116 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 38 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 116 2 7 19 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 116 (accept_3_2 13 38 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 116 2 6 19 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 116 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 38 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 116 2 5 19 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 116
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 9 38 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 116 2 4 19 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 116 (accept_3_2 7 38 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 116
  2 3 19 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  116 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 38 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 116 2 2 19 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 116 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 38 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 116 2 1 19 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 116 (accept_3_2 1 38 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 116)))))))))))))))))))))))))))))))))))))) (allB_succ 37 116 (allA_of_3_0 37 37 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 116 (allA_succ_of_accept 35 36 116
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 36 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 116 2 17 18 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 116 4 8 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 116 (accept_3_2 31 36 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 36 116 2 15 18 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 36 116 (Polychromatic418967fa.accept_19_10_17_2_1_5411 29 36 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 116 4 7 9 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 116
  (Polychromatic418967fa.accept_21_6_15_11_1_5410 27 36 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 116 2 13 18 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 116 (accept_3_2 25 36 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36
  116 4 6 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  36 116 (Polychromatic418967fa.accept_19_4_17_2_1_5409 23 36 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 36 116 2 11 18 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 36 116 (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 36 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 116 4 5 9 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 116 (accept_3_2 19 36 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 116 2 9 18 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 36 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 116 4 4 9 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 116
  (Polychromatic418967fa.accept_13_2_10_12_1_757 15 36 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 36 116 2 7 18 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 116 (accept_3_2 13 36 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36
  116 4 3 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  36 116 (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 36 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 36 116 2 5 18 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 36 116 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 36 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 116 4 2 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 116 (accept_3_2 7 36 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 116 2 3 18 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 36 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 36 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 116 4 1 9 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 116
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 116 2 1 18 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 116 (accept_3_2 1 36 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  116)))))))))))))))))))))))))))))))))))) (allB_succ 35 116 (allA_succ_of_accept 34 35 116 (accept_3_2 34 35 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  35 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 116
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 116 (accept_3_2 31 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 116 (Polychromatic418967fa.accept_17_13_1_14_1_1149 30 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 116 (Polychromatic418967fa.accept_10_9_5_6_1_691 29 35 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 116 (accept_3_2 28 35 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 116
  (Polychromatic418967fa.accept_11_4_2_6_1_389 26 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 116 (accept_3_2 25 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 116 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 116 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 35 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 116 (accept_3_2 22 35 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 35 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 116
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 20 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 116 (accept_3_2 19 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 116 (Polychromatic418967fa.accept_19_18_16_2_1_2858 18 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 116 (Polychromatic418967fa.accept_14_3_7_4_1_118 17 35 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 116 (accept_3_2 16 35 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 116
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 116 (accept_3_2 13 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 116 (Polychromatic418967fa.accept_16_12_3_4_1_4317 12 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 116 (Polychromatic418967fa.accept_10_1_5_6_1_649 11 35 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 116 (accept_3_2 10 35 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 116
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 8 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 116 (accept_3_2 7 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  116 (Polychromatic418967fa.accept_15_6_5_11_1_2378 6 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 35 116 (Polychromatic418967fa.accept_18_5_17_8_1_2984 5 35 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 116 (accept_3_2 4 35 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 116
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 116 (accept_3_2 1 35 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  116))))))))))))))))))))))))))))))))))) (allB_succ 34 116 (allA_of_3_0 34 34 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 116 (allA_succ_of_accept 32 33 116 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 33 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 116 (accept_3_2 31 33 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 30
  33 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 116 (accept_3_2 28 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 116 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 116 (Polychromatic418967fa.accept_19_7_14_2_1_4095 26 33 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 116 (accept_3_2 25 33 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 116 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 33
  116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 116 (accept_3_2 22 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 116 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 116 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 33 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 116 (accept_3_2 19 33 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 116 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 33 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 116 (accept_3_2 16 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 116 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 116 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 33 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 116 (accept_3_2 13 33 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 116 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 116 (accept_3_2 10 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 116 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 33 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 116 (accept_3_2 7 33 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 116 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 33 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 116
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 116 (accept_3_2 4 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  116 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 33 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 33 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 116 (accept_3_2 1 33 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 116))))))))))))))))))))))))))))))))) (allB_succ 32 116 (allA_succ_of_accept 31 32 116
  (accept_3_2 31 32 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 116 2 15 16 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 116
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 32 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 116 4 7 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 116 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 32 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 116 2 13 16 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 116 (accept_3_2 25 32 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 116 4 6 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 32 116 (Polychromatic418967fa.accept_13_10_6_12_1_2780 23 32 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 116 2 11 16 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 116
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 32 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 116 4 5 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 116 (accept_3_2 19 32 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  116 2 9 16 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 116 (Polychromatic418967fa.accept_22_17_10_6_1_5408 17 32 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 116 4 4 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 116 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 32 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 116 2 7 16 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 116 (accept_3_2 13 32 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 116 4 3 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 116 2 5 16 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 116
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 32 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 116 4 2 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 116 (accept_3_2 7 32 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 116
  2 3 16 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  116 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 32 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 32 116 4 1 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 32 116 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 32 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 116 2 1 16 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 116 (accept_3_2 1 32 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 32 116)))))))))))))))))))))))))))))))) (allB_succ 31 116 (allA_of_3_0 31 31 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 116 (allA_succ_of_accept 29 30 116
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 30 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 116 2 14 15 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 30 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 30 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 116 2 13 15 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 116 (accept_3_2 25 30 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 116 2 12 15 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 116 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 30 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 116 2 11 15 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 116
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 30 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 116 2 10 15 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 116 (accept_3_2 19 30 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30
  116 2 9 15 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  30 116 (Polychromatic418967fa.accept_16_1_14_4_1_3220 17 30 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 116 2 8 15 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 116 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 30 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 116 2 7 15 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 116 (accept_3_2 13 30 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 116 2 6 15 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 30 116 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 30 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 116 2 5 15 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 116
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 116 2 4 15 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 116 (accept_3_2 7 30 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 116
  2 3 15 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30
  116 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 30 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 116 2 2 15 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 30 116 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 30 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 116 2 1 15 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 116 (accept_3_2 1 30 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 116)))))))))))))))))))))))))))))) (allB_succ 29 116 (allA_succ_of_accept 28 29 116
  (accept_3_2 28 29 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 116
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 29 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 116 (accept_3_2 25 29 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 29 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 23
  29 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 116 (accept_3_2 22 29
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 116 (Polychromatic418967fa.accept_6_3_5_2_1_12
  21 29 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 116
  (Polychromatic418967fa.accept_21_20_8_11_1_5407 20 29 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 116 (accept_3_2 19 29 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 116 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 29 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 29 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 116 (accept_3_2 16 29 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 116
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 29 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 116 (accept_3_2 13 29 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 29 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 116 (Polychromatic418967fa.accept_14_11_1_4_1_4445 11 29 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 116 (accept_3_2 10 29 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 116
  (Polychromatic418967fa.accept_16_8_13_4_1_3258 8 29 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 116 (accept_3_2 7 29 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  116 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 29 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 29 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 116 (accept_3_2 4 29 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 116 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  29 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 116 (accept_3_2 1 29 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 116))))))))))))))))))))))))))))) (allB_succ 28 116 (allA_of_3_0
  28 28 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 116 (allA_succ_of_accept 26 27 116
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 27 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 116 (accept_3_2 25 27 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 27 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 116 (accept_3_2 22 27 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 116 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 27 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 116
  (Polychromatic418967fa.accept_19_1_8_2_1_2876 20 27 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 116 (accept_3_2 19 27 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 116 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 27 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 116 (accept_3_2 16 27 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 116 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 27 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 116
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 27 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 27 116 (accept_3_2 13 27 116 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 27 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 116 (accept_3_2 10 27 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 27
  116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 116
  (Polychromatic418967fa.accept_13_8_1_12_1_762 8 27 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 116 (accept_3_2 7 27 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  116 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 27 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 116 (accept_3_2 4 27 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 116 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 27
  116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 116 (accept_3_2 1 27 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 116))))))))))))))))))))))))))) (allB_succ 26 116
  (allA_succ_of_accept 25 26 116 (accept_3_2 25 26 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  116 2 12 13 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 26 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 116 2 11 13 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 116 (Polychromatic418967fa.accept_17_4_9_14_1_5406 21 26 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 116 2 10 13 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 116 (accept_3_2 19 26 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 116 2 9 13 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 116 (Polychromatic418967fa.accept_12_5_2_8_1_172 17
  26 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 116 2 8 13 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 116
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 26 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 116 2 7 13 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 116 (accept_3_2 13 26 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  116 2 6 13 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 116 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 26 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 116 2 5 13 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 26 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 116 2 4 13 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 116 (accept_3_2 7 26 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 116 2 3 13 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 116 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 26 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 116 2 2 13 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 116
  (Polychromatic418967fa.accept_31_3_26_23_1_5405 3 26 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 116 2 1 13 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 116 (accept_3_2 1 26 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  116)))))))))))))))))))))))))) (allB_succ 25 116 (allA_of_3_0 25 25 116 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 116 (allA_succ_of_accept 23 24 116 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 24 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 116 2 11 12 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 116
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 116 4 5 6 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 116 (accept_3_2 19 24 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  116 2 9 12 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 116 (Polychromatic418967fa.accept_13_4_11_12_1_1318 17 24 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 116 4 4 6 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 116 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 116 2 7 12 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 116 (accept_3_2 13 24 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 116 4 3 6 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 24 116 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 24 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 116 2 5 12 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 116
  (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 24 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 116 4 2 6 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 116 (accept_3_2 7 24 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 116
  2 3 12 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  116 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 24 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 116 4 1 6 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 116 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 116 2 1 12 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 116 (accept_3_2 1 24 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 116)))))))))))))))))))))))) (allB_succ 23 116 (allA_succ_of_accept 22 23 116 (accept_3_2 22
  23 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 116
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 23 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 116 (accept_3_2 19 23 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 116 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 23 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 116 (Polychromatic418967fa.accept_10_7_3_6_1_644
  17 23 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 116 (accept_3_2 16
  23 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 116
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 23 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 116 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 116 (accept_3_2 13 23 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 116 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 23 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 116 (Polychromatic418967fa.accept_8_3_7_4_1_42 11
  23 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 116 (accept_3_2 10 23
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 116 (Polychromatic418967fa.accept_6_3_5_2_1_12
  9 23 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 116
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 23 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 116 (accept_3_2 7 23 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  116 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 23 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 116 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 23 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 116 (accept_3_2 4 23 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 116 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 23
  116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 116 (accept_3_2 1 23 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 116))))))))))))))))))))))) (allB_succ 22 116 (allA_of_3_0 22 22
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 116 (allA_succ_of_accept 20 21 116
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 21 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 116 (accept_3_2 19 21 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 116 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 21 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 116 (accept_3_2 16 21 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 116 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 21 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 116
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 21 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 116 (accept_3_2 13 21 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 116 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 21 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 116 (accept_3_2 10 21 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 116 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 21 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 116
  (Polychromatic418967fa.accept_16_8_5_4_1_674 8 21 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 116 (accept_3_2 7 21 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  116 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 21 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 116 (accept_3_2 4 21 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 116 (Polychromatic418967fa.accept_14_3_7_4_1_118 3 21 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 116 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  21 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 116 (accept_3_2 1 21 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 116))))))))))))))))))))) (allB_succ 20 116 (allA_succ_of_accept
  19 20 116 (accept_3_2 19 20 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 116 2 9 10 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 116
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 20 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 116 4 4 5 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 116 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 20 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 116 2 7 10 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 116 (accept_3_2 13 20 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 116 4 3 5 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 116 (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 20 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 116 2 5 10 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 116
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 20 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 116 4 2 5 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 116 (accept_3_2 7 20 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 116
  2 3 10 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  116 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 20 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 116 4 1 5 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 116 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 20 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 116 2 1 10 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 116 (accept_3_2 1 20 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 116)))))))))))))))))))) (allB_succ 19 116 (allA_of_3_0 19 19 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 116 (allA_succ_of_accept 17 18 116 (Polychromatic418967fa.accept_13_4_5_12_1_751 17 18 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 116 2 8 9 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 116
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 18 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 116 2 7 9 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 116 (accept_3_2 13 18 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  116 2 6 9 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 116 (Polychromatic418967fa.accept_20_11_18_16_1_1559 11 18 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 116 2 5 9 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 116 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 18 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 116 2 4 9 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 116 (accept_3_2 7 18 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 116 2 3 9 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 116 (Polychromatic418967fa.accept_19_5_18_2_1_5404 5 18 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 116 2 2 9 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 116
  (Polychromatic418967fa.accept_10_3_8_6_1_326 3 18 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 116 2 1 9 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 116 (accept_3_2 1 18 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  116)))))))))))))))))) (allB_succ 17 116 (allA_succ_of_accept 16 17 116 (accept_3_2 16 17 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 17 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 116
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 17 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 116 (accept_3_2 13 17 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 116 (Polychromatic418967fa.accept_16_12_1_4_1_5403 12 17 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 116 (Polychromatic418967fa.accept_10_1_7_6_1_91 11 17 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 116 (accept_3_2 10 17 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 116
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 17 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 116 (accept_3_2 7 17 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  116 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 17 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 116 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 17 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 116 (accept_3_2 4 17 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 116 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  17 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 116 (accept_3_2 1 17 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 116))))))))))))))))) (allB_succ 16 116 (allA_of_3_0 16 16 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 116 (allA_succ_of_accept 14 15 116
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 15 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 116 (accept_3_2 13 15 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 116 (accept_3_2 10 15 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 116 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 15 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 116
  (Polychromatic418967fa.accept_16_8_15_4_1_5402 8 15 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 116 (accept_3_2 7 15 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  116 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 15 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 15 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 116 (accept_3_2 4 15 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 116 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  15 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 116 (accept_3_2 1 15 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 116))))))))))))))) (allB_succ 14 116 (allA_succ_of_accept 13 14
  116 (accept_3_2 13 14 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 116 2 6 7 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 116
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 14 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 116 2 5 7 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 116 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 14 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 116 2 4 7 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 116 (accept_3_2 7 14 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 116 2 3 7 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 116 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 14 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 116 2 2 7 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 116 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 14
  116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 116 2 1 7 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 116 (accept_3_2 1 14
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 116)))))))))))))) (allB_succ 13 116 (allA_of_3_0 13 13 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 116 (allA_succ_of_accept 11 12 116
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 12 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 116 2 5 6 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 12 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 116 4 2 3 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 116 (accept_3_2 7 12 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 116 2 3 6 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 116 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 116 4 1 3 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 116 (Polychromatic418967fa.accept_16_3_12_4_1_170 3
  12 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 116 2 1 6 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 116 (accept_3_2 1 12
  116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 116)))))))))))) (allB_succ 11 116 (allA_succ_of_accept 10 11
  116 (accept_3_2 10 11 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 116
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 116 (Polychromatic418967fa.accept_14_8_11_4_1_3438 8 11 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 116 (accept_3_2 7 11 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 116 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 11 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 116 (Polychromatic418967fa.accept_9_5_2_8_1_109 5
  11 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 116 (accept_3_2 4 11 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 116
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 11 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 116 (accept_3_2 1 11 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  116))))))))))) (allB_succ 10 116 (allA_of_3_0 10 10 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 116
  (allA_succ_of_accept 8 9 116 (Polychromatic418967fa.accept_13_8_9_12_1_2813 8 9 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 116 (accept_3_2 7 9 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 116 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 9 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 116 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 116 (accept_3_2 4 9 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 116 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 9
  116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 116
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 2 9 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 116 (accept_3_2 1 9 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 116)))))))))
  (allB_succ 8 116 (allA_succ_of_accept 7 8 116 (accept_3_2 7 8 116 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 116 2 3 4 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 116 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 8 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 116 4 1 2 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 116 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 8 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 116 2 1 4 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 116 (accept_3_2 1 8 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 116)))))))) (allB_succ 7 116 (allA_of_3_0 7 7 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 116 (allA_succ_of_accept 5 6 116 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 6 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 116 2 2 3 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 116
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 6 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 116 2 1 3 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 116 (accept_3_2 1 6 116 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 116))))))
  (allB_succ 5 116 (allA_succ_of_accept 4 5 116 (accept_3_2 4 5 116 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 116 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 116 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 5 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 116 (accept_3_2 1 5 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 116))))) (allB_succ 4 116 (allA_of_3_0 4 4 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 116 (allA_succ_of_accept 2 3 116 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 3 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 116 (accept_3_2 1 3 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 116))) (allB_succ 2 116 (allA_succ_of_accept 1 2 116 (accept_3_2 1 2 116
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 116)) (allB_two
  116))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


