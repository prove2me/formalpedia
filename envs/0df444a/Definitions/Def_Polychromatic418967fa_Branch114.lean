-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch114
-- name    : Polychromatic418967fa_Branch114
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:11:33.87429+00:00
-- url     : https://prove2.me/theorems/fba94a2b-75dc-4df2-a7b5-a5516cc11db5
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

def Polychromatic418967fa.branch_114 : allB 114 114 :=
  allB_succ' 2 113 114 (Eq.refl Bool.true) (allA_succ_of_accept 1 113 114 (accept_3_4 1 113 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 114)) (allB_succ' 3 112 114 (Eq.refl Bool.true) (allA_succ_of_gcd 2 112 114 2 1 56
  57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 114
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 112 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 112 114))) (allB_succ' 4 111 114 (Eq.refl Bool.true) (allA_succ_of_gcd 3 111 114 3 1 37 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 114
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 111 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 111 114)))) (allB_succ' 5 110 114 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  110 114 2 2 55 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 110 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 110 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 110 114 2 1 55 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 110 114 (accept_3_4 1 110 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  114))))) (allB_succ' 6 109 114 (Eq.refl Bool.true) (allA_succ_of_accept 5 109 114 (accept_3_5 5 109 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 114 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 109 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 114 (accept_3_5 2 109 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 114 (Polychromatic418967fa.accept_23_1_17_22_1_5357 1 109 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 114)))))) (allB_succ' 7 108 114 (Eq.refl Bool.true) (allA_succ_of_gcd 6 108 114 6 1 18 19
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 114
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 108 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 108 114 2 2 54 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 108 114 3 1 36 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 108 114 2 1 54 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 108 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108 114))))))) (allB_succ' 8 107 114 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 107 114 (accept_3_4 7 107 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 114 (Polychromatic418967fa.accept_13_6_3_10_1_698 6 107 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 114 (accept_3_4 4 107 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 107 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 114
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 107 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 114 (accept_3_4 1 107 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  114)))))))) (allB_succ' 9 106 114 (Eq.refl Bool.true) (allA_succ_of_gcd 8 106 114 2 4 53 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 114
  (Polychromatic418967fa.accept_15_7_1_9_1_1500 7 106 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 106 114 2 3 53 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 106 114 (accept_3_5 5 106 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106
  114 2 2 53 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  106 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 106 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 106 114 2 1 53 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 106 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 106 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 114))))))))) (allB_succ' 10 105 114 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 105 114 3 3 35 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 105 114 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 105 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 105 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 114 3 2 35 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 105 114
  (Polychromatic418967fa.accept_14_5_7_2_1_468 5 105 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 114 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 105 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 114 3 1 35 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 114 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 105 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 114
  (Polychromatic418967fa.accept_10_1_5_4_1_276 1 105 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 105 114)))))))))) (allB_succ' 11 104 114 (Eq.refl Bool.true) (allA_succ_of_gcd 10 104 114 2 5 52 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 114
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 104 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 104 114 2 4 52 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 114 (accept_3_4 7 104 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104
  114 2 3 52 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  104 114 (Polychromatic418967fa.accept_15_5_14_9_1_274 5 104 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 104 114 2 2 52 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 104 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 104 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 114 2 1 52 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 114 (accept_3_4 1 104 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104 114))))))))))) (allB_succ' 12 103 114 (Eq.refl Bool.true) (allA_succ_of_accept 11
  103 114 (accept_3_5 11 103 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 114
  (Polychromatic418967fa.accept_7_3_5_2_1_17 10 103 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 103 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 114 (accept_3_5 8 103 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 103 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 103 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 114 (Polychromatic418967fa.accept_13_6_12_10_1_690
  6 103 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 114 (accept_3_5 5
  103 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 114
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 103 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 103 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 103 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 114 (accept_3_5 2 103 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 103 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 114)))))))))))) (allB_succ' 13 102 114 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 102 114 6 2 17 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 102 114 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 102 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 114 2 5 51 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 102 114 3 3 34 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 102 114 2 4 51 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 114 (Polychromatic418967fa.accept_9_7_3_6_1_270 7
  102 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 114 6 1 17 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 114
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 102 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 102 114 2 2 51 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 102 114 3 1 34 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 102 114 2 1 51 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 102 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 102 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 102 114))))))))))))) (allB_succ' 14 101 114 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 101 114 (accept_3_4 13 101 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 101 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 114 (accept_3_4 10 101 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 114 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 101 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 114
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 101 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 114 (accept_3_4 7 101 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 101 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 101 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 114 (accept_3_4 4 101 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 114
  (Polychromatic418967fa.accept_15_2_11_9_1_263 2 101 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 114 (accept_3_4 1 101 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  114)))))))))))))) (allB_succ' 15 100 114 (Eq.refl Bool.true) (allA_succ_of_gcd 14 100 114 2 7 50 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 114
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 100 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 100 114 2 6 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 100 114 (accept_3_5 11 100 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  100 114 2 5 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 100 114 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 100 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 100 114 2 4 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 100 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 100 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 114 2 3 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 100 114 (accept_3_5 5 100 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100 114 2 2 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 100 114 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 100 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 114 2 1 50 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 114
  (Polychromatic418967fa.accept_13_1_9_10_1_625 1 100 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 100 114))))))))))))))) (allB_succ' 16 99 114 (Eq.refl Bool.true) (allA_succ_of_gcd 15 99 114 3 5 33 38
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 99 114
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 99 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 114 3 4 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 114 (Polychromatic418967fa.accept_13_11_8_10_1_676 11 99 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 114
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 99 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 99 114 3 3 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 99 114 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 99 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 114 (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 99 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 114 3 2 33 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 114 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 99 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 114 3 1 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 114 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 99 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 99 114)))))))))))))))) (allB_succ' 17 98 114 (Eq.refl Bool.true) (allA_succ_of_gcd 16 98 114 2 8 49 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 114
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 98 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 98 114 2 7 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 98 114 (accept_3_4 13 98 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98
  114 2 6 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  98 114 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 98 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 98 114 2 5 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 98 114 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 98 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 114 2 4 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 114 (accept_3_4 7 98 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 114 2 3 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 98 114 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 98 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 114 2 2 49 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 114
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 98 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 98 114 2 1 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 98 114 (accept_3_4 1 98 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  114))))))))))))))))) (allB_succ' 18 97 114 (Eq.refl Bool.true) (allA_succ_of_accept 17 97 114 (accept_3_5 17 97 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 114 (Polychromatic418967fa.accept_13_3_6_10_1_2658
  16 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 114 (accept_3_5 14 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 114 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 97 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 114 (accept_3_5 11 97 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 97 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 114
  (Polychromatic418967fa.accept_13_9_6_10_1_666 9 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 114 (accept_3_5 8 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 97 114 (Polychromatic418967fa.accept_16_6_1_2_1_3129 6 97 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 114 (accept_3_5 5 97 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 97 114 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 97 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 114 (accept_3_5 2 97 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 97
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 114)))))))))))))))))) (allB_succ' 19 96
  114 (Eq.refl Bool.true) (allA_succ_of_gcd 18 96 114 6 3 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 96 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 114 2 8 48 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 96 114 3 5 32 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 96 114 2 7 48 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 114
  (Polychromatic418967fa.accept_17_13_11_12_1_4131 13 96 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 96 114 6 2 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 96 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 96 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 114 2 5 48 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 96 114 3 3 32 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 96 114 2 4 48 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 114 (Polychromatic418967fa.accept_11_7_8_4_1_718 7
  96 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 114 6 1 16 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 114
  (Polychromatic418967fa.accept_10_5_6_4_1_64 5 96 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 114 2 2 48 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 96 114 3 1 32 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 96 114 2 1 48 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 114 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 96 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96 114))))))))))))))))))) (allB_succ' 20 95 114 (Eq.refl Bool.true)
  (allA_succ_of_gcd 19 95 114 19 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 18 95 114 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 95 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 114 (accept_3_4 16 95 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 114 (Polychromatic418967fa.accept_18_15_5_6_1_5293
  15 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 114
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 114 (accept_3_4 13 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 114 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 95 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 114 (accept_3_4 10 95 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 114
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 114 (accept_3_4 7 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  114 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 95 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 114 (accept_3_4 4 95 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 95 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 114 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  95 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 114 (accept_3_4 1 95 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95 114)))))))))))))))))))) (allB_succ' 21 94 114 (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 94 114 2 10 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 94 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 94 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 114 2 9 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 114 (accept_3_5 17 94 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94 114 2 8 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 94 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 94 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 114 2 7 47 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 114
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 94 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 94 114 2 6 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 94 114 (accept_3_5 11 94 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94
  114 2 5 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  94 114 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 94 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 94 114 2 4 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 94 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 94 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 114 2 3 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 114 (accept_3_5 5 94 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 114 2 2 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 94 114 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 94 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 114 2 1 47 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 114
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 94 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 114))))))))))))))))))))) (allB_succ' 22 93 114 (Eq.refl Bool.true) (allA_succ_of_gcd 21 93 114 3 7 31 38
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 93 114
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 114 3 6 31 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 114 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 93 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 114
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 93 114 3 5 31 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 93 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 93 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 114 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 93 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 114 3 4 31 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 93 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 114 3 3 31 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 114 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 93 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 93 114 3 2 31 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 93 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 93 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 114 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 93 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 114 3 1 31 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 114
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 93 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 93 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 93 114)))))))))))))))))))))) (allB_succ' 23 92 114 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 92 114 2 11 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 92 114 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 92 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 114 2 10 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 114 (accept_3_4 19 92 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92 114 2 9 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 92 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 92 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 92 114 2 8 46 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 114
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 92 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 92 114 2 7 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 92 114 (accept_3_4 13 92 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92
  114 2 6 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  92 114 (Polychromatic418967fa.accept_13_11_1_10_1_648 11 92 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 92 114 2 5 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 92 114 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 92 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 114 2 4 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 114 (accept_3_4 7 92 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 114 2 3 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 92 114 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 92 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 114 2 2 46 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 114
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 92 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 92 114 2 1 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 92 114 (accept_3_4 1 92 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  114))))))))))))))))))))))) (allB_succ' 24 91 114 (Eq.refl Bool.true) (allA_succ_of_accept 23 91 114 (accept_3_5 23 91
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 114
  (Polychromatic418967fa.accept_9_4_1_6_1_284 22 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 91 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 91 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 114 (accept_3_5 20 91 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 91 114 (Polychromatic418967fa.accept_14_5_7_2_1_468 19 91 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 114 (Polychromatic418967fa.accept_11_7_3_4_1_729
  18 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 114 (accept_3_5 17
  91 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 114
  (Polychromatic418967fa.accept_9_7_1_6_1_261 16 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 91 114 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 91 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 114 (accept_3_5 14 91 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 91 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 91 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 114 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 114 (accept_3_5 11 91
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 114
  (Polychromatic418967fa.accept_15_10_1_9_1_5356 10 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 91 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 114 (accept_3_5 8 91 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 91 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 91 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 114 (Polychromatic418967fa.accept_15_6_1_9_1_1476 6
  91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 114 (accept_3_5 5 91 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 114 (Polychromatic418967fa.accept_9_4_1_6_1_284 4
  91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 114
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 114 (accept_3_5 2 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 91 114)))))))))))))))))))))))) (allB_succ' 25 90 114 (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 114 6 4 15
  19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 114
  (Polychromatic418967fa.accept_21_2_6_9_1_5355 23 90 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 114 2 11 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 90 114 3 7 30 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 90 114 2 10 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 114 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 90 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 114 6 3 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 90 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 114 2 8 45 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 114 3 5 30 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 114 2 7 45 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 114
  (Polychromatic418967fa.accept_21_13_6_9_1_1328 13 90 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 90 114 6 2 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 90 114 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 90 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 114 2 5 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 90 114 3 3 30 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 90 114 2 4 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 114 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 90 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 114 6 1 15 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 114
  (Polychromatic418967fa.accept_20_5_10_14_1_5317 5 90 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 90 114 2 2 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 90 114 3 1 30 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 90 114 2 1 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 90 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90 114))))))))))))))))))))))))) (allB_succ' 26 89 114 (Eq.refl Bool.true)
  (allA_succ_of_accept 25 89 114 (accept_3_4 25 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 114 (accept_3_4 22 89 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 89 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 114
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 114 (accept_3_4 19 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 89 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 114 (accept_3_4 16 89 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 114
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 114 (accept_3_4 13 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 114 (accept_3_4 10 89 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 114 (Polychromatic418967fa.accept_17_9_4_12_1_2958 9 89 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 114
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 114 (accept_3_4 7 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  114 (Polychromatic418967fa.accept_15_6_14_9_1_1471 6 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 89 114 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 89 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 114 (accept_3_4 4 89 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 89 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 114
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 89 114 (accept_3_4 1 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89
  114)))))))))))))))))))))))))) (allB_succ' 27 88 114 (Eq.refl Bool.true) (allA_succ_of_gcd 26 88 114 2 13 44 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 114
  (Polychromatic418967fa.accept_17_8_3_12_1_5354 25 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 88 114 2 12 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 88 114 (accept_3_5 23 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88
  114 2 11 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  88 114 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 88 114 2 10 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 88 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 88 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 114 2 9 44 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 114 (accept_3_5 17 88 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88 114 2 8 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 88 114 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 88 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 114 2 7 44 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 114
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 88 114 2 6 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 88 114 (accept_3_5 11 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88
  114 2 5 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  88 114 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 88 114 2 4 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 88 114 (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 88 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 114 2 3 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 114 (accept_3_5 5 88 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 114 2 2 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 88 114 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 88 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 114 2 1 44 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 114
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 114))))))))))))))))))))))))))) (allB_succ' 28 87 114 (Eq.refl Bool.true) (allA_succ_of_gcd 27 87 114 3 9
  29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 114
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 87 114 3 8 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 87 114 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 87 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 114
  (Polychromatic418967fa.accept_7_1_3_2_1_13 22 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 87 114 3 7 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 87 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 87 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 87 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 114 3 6 29 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 114 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 87 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 87 114 3 5 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 87 114 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 87 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 87 114 3 4 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 87 114 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 87 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 114 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 87 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 114 3 3 29 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 114
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 114 (Polychromatic418967fa.accept_17_7_2_12_1_1069 7 87 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 114 3 2 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 114
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 87 114 3 1 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 87 114 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 87 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 114)))))))))))))))))))))))))))) (allB_succ'
  29 86 114 (Eq.refl Bool.true) (allA_succ_of_gcd 28 86 114 2 14 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 114 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 86 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 114 2 13 43 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 114 (accept_3_4 25
  86 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 114 2 12 43 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 114
  (Polychromatic418967fa.accept_17_6_1_12_1_4115 23 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 86 114 2 11 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 86 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 86 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 114 2 10 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 114 (accept_3_4 19 86 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 114 2 9 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 86 114 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 86 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 114 2 8 43 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 114
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 114 2 7 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 114 (accept_3_4 13 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  114 2 6 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 114 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 114 2 5 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 114 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 86 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 114 2 4 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 114 (accept_3_4 7 86 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 114 2 3 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 114 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 86 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 114 2 2 43 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 114
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 114 2 1 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 114 (accept_3_4 1 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  114))))))))))))))))))))))))))))) (allB_succ' 30 85 114 (Eq.refl Bool.true) (allA_succ_of_accept 29 85 114 (accept_3_5
  29 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 114
  (Polychromatic418967fa.accept_9_1_4_6_1_5 28 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 85 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 114 (accept_3_5 26 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 85 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 85 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 24
  85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 114 (accept_3_5 23 85
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 114
  (Polychromatic418967fa.accept_14_8_1_2_1_965 22 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 85 114 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 114 (accept_3_5 20 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 85 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 114 (Polychromatic418967fa.accept_11_7_8_4_1_718
  18 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 114 (accept_3_5 17
  85 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 114
  (Polychromatic418967fa.accept_9_7_4_6_1_273 16 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 85 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 114 (accept_3_5 14 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 85 114 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 85 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 114 (Polychromatic418967fa.accept_9_3_4_6_1_252 12
  85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 114 (accept_3_5 11 85
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 114
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 85 114 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 114 (accept_3_5 8 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 85 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 114 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 114 (accept_3_5 5 85 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 114 (Polychromatic418967fa.accept_13_4_7_10_1_1200
  4 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 114 (accept_3_5 2 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85
  114 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 85 114)))))))))))))))))))))))))))))) (allB_succ' 31 84 114 (Eq.refl Bool.true) (allA_succ_of_gcd 30 84 114 6
  5 14 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 114
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 84 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 114 2 14 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 84 114 3 9 28 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 84 114 2 13 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 84 114 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 84 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 114 6 4 14 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 84 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 114 2 11 42 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 84 114 3 7 28 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 84 114 2 10 42 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 114
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 84 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 114 6 3 14 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 114 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 84 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 114 2 8 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 84 114 3 5 28 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 84 114 2 7 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 114 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 84 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 114 6 2 14 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 114
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 84 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 84 114 2 5 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 84 114 3 3 28 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 84 114 2 4 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 114 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 84 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 114 6 1 14 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 84 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 114 2 2 42 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 84 114 3 1 28 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 84 114 2 1 42 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 114
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 84 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 114))))))))))))))))))))))))))))))) (allB_succ' 32 83 114 (Eq.refl Bool.true) (allA_succ_of_accept 31 83
  114 (accept_3_4 31 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 114
  (Polychromatic418967fa.accept_9_3_2_6_1_264 30 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 83 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 114 (accept_3_4 28 83 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 83 114 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 83 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 114 (Polychromatic418967fa.accept_9_8_2_6_1_875 26
  83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 114 (accept_3_4 25 83
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 114 (Polychromatic418967fa.accept_7_3_6_2_1_90
  24 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 114
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 114 (accept_3_4 22 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 114 (Polychromatic418967fa.accept_17_3_15_12_1_5353 20 83 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 114 (accept_3_4 19 83 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 114 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 83 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 114 (accept_3_4 16 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 114 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 83 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 114 (accept_3_4 13 83 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 114 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 83 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 114
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 114 (accept_3_4 10 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 83 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 83 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 114 (accept_3_4 7 83 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 83 114 (Polychromatic418967fa.accept_13_6_5_10_1_1213 6 83 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 114 (accept_3_4 4 83 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 83
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 114
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 114 (accept_3_4 1 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  114)))))))))))))))))))))))))))))))) (allB_succ' 33 82 114 (Eq.refl Bool.true) (allA_succ_of_gcd 32 82 114 2 16 41 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 114
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 114 2 15 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 82 114 (accept_3_5 29 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82
  114 2 14 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  82 114 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 82 114 2 13 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 82 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 82 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 114 2 12 41 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 114 (accept_3_5 23 82 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 114 2 11 41 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 114
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 82 114 2 10 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 82 114 (Polychromatic418967fa.accept_13_6_4_10_1_660 19 82 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 114 2 9 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 114 (accept_3_5 17 82 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 82 114 2 8 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 82 114 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 82 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 114 2 7 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 114 (Polychromatic418967fa.accept_9_4_1_6_1_284 13
  82 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 114 2 6 41 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 114 (accept_3_5 11
  82 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 114 2 5 41 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 114
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 114 2 4 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 82 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 114 2 3 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 114 (accept_3_5 5 82 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 114 2 2 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 82 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 114 2 1 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 114 (Polychromatic418967fa.accept_13_1_4_10_1_622 1
  82 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 114)))))))))))))))))))))))))))))))))
  (allB_succ' 34 81 114 (Eq.refl Bool.true) (allA_succ_of_gcd 33 81 114 3 11 27 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 114
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 114 3 10 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 114 (Polychromatic418967fa.accept_15_14_6_9_1_2274
  29 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 114
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 114 3 9 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 81 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 114 (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 81 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 114 3 8 27 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 114 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 81 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 114 3 7 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 114 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 81 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 114 3 6 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 114 (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 81 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 114 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 81 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 114 3 5 27 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 114
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 114 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 81 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 114 3 4 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 114
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 114 3 3 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 114 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 81 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 114 3 2 27 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 114
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 114 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 81 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 114 3 1 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 114 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 81 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 114
  (Polychromatic418967fa.accept_15_1_6_9_1_254 1 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 114)))))))))))))))))))))))))))))))))) (allB_succ' 35 80 114 (Eq.refl Bool.true) (allA_succ_of_gcd 34 80
  114 2 17 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  80 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 80 114 2 16 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 80 114 (accept_3_4 31 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 80 114 2 15 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 80 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 80 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 80 114 2 14 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 80 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 27
  80 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 114 2 13 40 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 114 (accept_3_4 25
  80 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 114 2 12 40 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 114
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 80 114 2 11 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 80 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 80 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 114 2 10 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 114 (accept_3_4 19 80 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80 114 2 9 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 80 114 (Polychromatic418967fa.accept_25_17_5_14_1_5352 17 80 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 114 2 8 40 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 80 114
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 80 114 2 7 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 80 114 (accept_3_4 13 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80
  114 2 6 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  80 114 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 80 114 2 5 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 80 114 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 80 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 114 2 4 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 114 (accept_3_4 7 80 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 114 2 3 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 80 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 80 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 114 2 2 40 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 114
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 80 114 2 1 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 80 114 (accept_3_4 1 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  114))))))))))))))))))))))))))))))))))) (allB_succ' 36 79 114 (Eq.refl Bool.true) (allA_succ_of_accept 35 79 114
  (accept_3_5 35 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 114
  (Polychromatic418967fa.accept_21_13_16_9_1_2541 34 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 79 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 114 (accept_3_5 32 79 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 79 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 79 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 114 (Polychromatic418967fa.accept_9_3_7_6_1_76 30
  79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 114 (accept_3_5 29 79
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 114 (Polychromatic418967fa.accept_9_1_7_6_1_75
  28 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 114
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 27 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 114 (accept_3_5 26 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 114 (Polychromatic418967fa.accept_13_11_1_10_1_648 24 79 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 114 (accept_3_5 23 79 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 79 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 114 (accept_3_5 20 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 114 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 79 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 114 (accept_3_5 17 79 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 114 (Polychromatic418967fa.accept_17_16_11_12_1_2008 16 79 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 114
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 114 (accept_3_5 14 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 114 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 79 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 114 (accept_3_5 11 79 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 79 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 114 (accept_3_5 8 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  114 (Polychromatic418967fa.accept_14_7_9_2_1_2489 7 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 114 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 79 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 114 (accept_3_5 5 79 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 79 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 114
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 114 (accept_3_5 2 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 114)))))))))))))))))))))))))))))))))))) (allB_succ' 37 78 114 (Eq.refl Bool.true) (allA_succ_of_gcd 36 78
  114 6 6 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  78 114 (Polychromatic418967fa.accept_15_5_3_9_1_283 35 78 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 78 114 2 17 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 78 114 3 11 26 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 78 114 2 16 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 78 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 78 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 114 6 5 13 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 114
  (Polychromatic418967fa.accept_10_9_8_4_1_970 29 78 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 114 2 14 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 78 114 3 9 26 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 78 114 2 13 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 78 114 (Polychromatic418967fa.accept_15_10_3_9_1_3285 25 78 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 114 6 4 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 114 (Polychromatic418967fa.accept_15_8_3_9_1_4220 23 78 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 114 2 11 39 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 78 114 3 7 26 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 78 114 2 10 39 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 114
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 78 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 114 6 3 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 78 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 114 2 8 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 78 114 3 5 26 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 78 114 2 7 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 114 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 78 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 114 6 2 13 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 114
  (Polychromatic418967fa.accept_21_11_15_9_1_3868 11 78 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 114 2 5 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 78 114 3 3 26 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 78 114 2 4 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 114 (Polychromatic418967fa.accept_21_7_15_9_1_5289 7 78 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 114 6 1 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 114 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 78 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 114 2 2 39 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 78 114 3 1 26 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 78 114 2 1 39 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 114
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 1 78 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 114))))))))))))))))))))))))))))))))))))) (allB_succ' 38 77 114 (Eq.refl Bool.true) (allA_succ_of_accept
  37 77 114 (accept_3_4 37 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 114
  (Polychromatic418967fa.accept_21_15_14_9_1_2540 36 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 77 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 77 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 77 114 (accept_3_4 34 77 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 77 114 (Polychromatic418967fa.accept_10_3_7_4_1_584 33 77 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 114 (Polychromatic418967fa.accept_10_2_7_4_1_967
  32 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 114 (accept_3_4 31
  77 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 114
  (Polychromatic418967fa.accept_9_3_5_6_1_253 30 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 77 114 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 77 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 114 (accept_3_4 28 77 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 77 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 77 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 114 (Polychromatic418967fa.accept_9_8_5_6_1_538 26
  77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 114 (accept_3_4 25 77
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 114
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 114 (accept_3_4 22 77 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 77 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 77 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 114
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 114 (accept_3_4 19 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 114 (Polychromatic418967fa.accept_21_18_14_9_1_5351 18 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 114 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 77 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 114 (accept_3_4 16 77 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 114
  (Polychromatic418967fa.accept_17_14_9_12_1_5350 14 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 114 (accept_3_4 13 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 77 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 114 (accept_3_4 10 77 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 114 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 77 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 114
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 114 (accept_3_4 7 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77
  114 (Polychromatic418967fa.accept_13_6_12_10_1_690 6 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 77 114 (Polychromatic418967fa.accept_14_5_7_2_1_468 5 77 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 114 (accept_3_4 4 77 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 114
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 114 (accept_3_4 1 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  114)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 76 114 (Eq.refl Bool.true) (allA_succ_of_gcd 38 76 114 38 1 2
  3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 76 114
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 76 114 2 18 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 76 114 (accept_3_5 35 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76
  114 2 17 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  76 114 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 76 114 2 16 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 76 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 76 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 76 114 2 15 38 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 76 114 (accept_3_5 29 76 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76 114 2 14 38 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 76 114
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 76 114 2 13 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 76 114 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 76 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 114 2 12 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 114 (accept_3_5 23 76 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 114 2 11 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 114 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 76 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 114 2 10 38 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 19 76 114 19 1 4 6 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 18 76 114 2 9 38 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 114 (accept_3_5 17
  76 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76 114 2 8 38 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 76 114
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 76 114 2 7 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 76 114 (Polychromatic418967fa.accept_25_13_1_14_1_5349 13 76 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 114 2 6 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 114 (accept_3_5 11 76 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 76 114 2 5 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 76 114 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 76 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 114 2 4 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 76
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 114 2 3 38 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 114 (accept_3_5 5 76
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 114 2 2 38 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76 114
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 114 2 1 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 76 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76 114))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 75 114 (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 75 114 3 13 25 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 75 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 75 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 114 3 12 25 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 114
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 114 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 75 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 114 3 11 25 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 114
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 114 3 10 25 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 75 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 114 3 9 25 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 114
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 75 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 114 3 8 25 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 75 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 114
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 114 3 7 25 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 114 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 75 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 75 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 114 3 6 25 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 114 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 75 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 114 3 5 25 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 75 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 114 3 4 25 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 75 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 75 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 114 3 3 25 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 114
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 114 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 75 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 114 3 2 25 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 114
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 114 3 1 25 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 114 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 75 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 114))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 74 114 (Eq.refl Bool.true) (allA_succ_of_gcd 40 74 114 2 20 37 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 114
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 74 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 114 2 19 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 74 114 (accept_3_4 37 74 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74
  114 2 18 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  74 114 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 74 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 74 114 2 17 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 74 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 74 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 114 2 16 37 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 114 (accept_3_4 31 74 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 114 2 15 37 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 114
  (Polychromatic418967fa.accept_11_7_8_4_1_718 29 74 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 74 114 2 14 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 74 114 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 74 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 74 114 2 13 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 74 114 (accept_3_4 25 74 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74 114 2 12 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 74 114 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 74 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 114 2 11 37 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 114
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 74 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 114 2 10 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 74 114 (accept_3_4 19 74 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74
  114 2 9 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  74 114 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 74 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 74 114 2 8 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 74 114 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 74 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 114 2 7 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 114 (accept_3_4 13 74 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 114 2 6 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 74 114 (Polychromatic418967fa.accept_17_11_6_12_1_5348 11 74 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 74 114 2 5 37 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 74 114
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 74 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 74 114 2 4 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 74 114 (accept_3_4 7 74 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 114
  2 3 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 74
  114 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 74 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 74 114 2 2 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 74 114 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 74 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 114 2 1 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 114 (accept_3_4 1 74 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 114))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 73 114 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 73 114 (accept_3_5 41 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 114 (accept_3_5 38 73 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 114 (Polychromatic418967fa.accept_10_7_3_4_1_978 37 73 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 114
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 114 (accept_3_5 35 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 73 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 114 (accept_3_5 32 73 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 114
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 114 (accept_3_5 29 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 114 (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 114 (accept_3_5 26 73 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 73 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 114
  (Polychromatic418967fa.accept_13_11_8_10_1_676 24 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 114 (accept_3_5 23 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 114 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 73 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 114 (accept_3_5 20 73 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 114
  (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 114 (accept_3_5 17 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 114 (accept_3_5 14 73 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 73 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 114
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 114 (accept_3_5 11 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 114 (Polychromatic418967fa.accept_17_10_5_12_1_4101 10 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 114 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 73 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 114 (accept_3_5 8 73 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 114
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 114 (accept_3_5 5 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  114 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 73 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 114 (accept_3_5 2 73 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 73 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 114)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 72
  114 (Eq.refl Bool.true) (allA_succ_of_gcd 42 72 114 6 7 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 114 (Polychromatic418967fa.accept_17_7_4_12_1_4084 41 72 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 114 2 20 36 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 72 114 3 13 24 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 72 114 2 19 36 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 114
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 72 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 114 6 6 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 114 (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 72 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 114 2 17 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 72 114 3 11 24 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 72 114 2 16 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 114 (Polychromatic418967fa.accept_22_9_6_4_1_5347
  31 72 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 114 6 5 12 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 114
  (Polychromatic418967fa.accept_13_3_7_10_1_668 29 72 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 72 114 2 14 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 72 114 3 9 24 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 72 114 2 13 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 72 114 (Polychromatic418967fa.accept_13_12_7_10_1_2662 25 72 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 114 6 4 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 114 (Polychromatic418967fa.accept_25_23_22_14_1_5346 23 72
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 114 2 11 36 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 72 114 3 7 24 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 72 114 2 10 36 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 114
  (Polychromatic418967fa.accept_15_4_12_9_1_773 19 72 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 114 6 3 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 114 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 72 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 114 2 8 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 72 114 3 5 24 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 72 114 2 7 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 114 (Polychromatic418967fa.accept_11_2_6_4_1_3028 13 72 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 114 6 2 12 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 114
  (Polychromatic418967fa.accept_22_11_6_4_1_5345 11 72 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 72 114 2 5 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 72 114 3 3 24 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 72 114 2 4 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 114 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 72 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 114 6 1 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 114 (Polychromatic418967fa.accept_15_5_12_9_1_2253 5 72 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 114 2 2 36 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 72 114 3 1 24 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 72 114 2 1 36 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 114
  (Polychromatic418967fa.accept_25_1_22_14_1_5344 1 72 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 114))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 71 114 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 71 114 (accept_3_4 43 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 114 (Polychromatic418967fa.accept_13_3_6_10_1_2658 42 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 114 (accept_3_4 40 71 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 71 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 114
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 114 (accept_3_4 37 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 114 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 114 (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 71 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 114 (accept_3_4 34 71 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 114
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 114 (accept_3_4 31 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 114 (accept_3_4 28 71 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 114 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 71 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 114
  (Polychromatic418967fa.accept_20_6_11_14_1_5343 26 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 114 (accept_3_4 25 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 114 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 71 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 114 (accept_3_4 22 71 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 114
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 114 (accept_3_4 19 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 114 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 114 (accept_3_4 16 71 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 114 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 71 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 114
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 114 (accept_3_4 13 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 114 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 71 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 114 (accept_3_4 10 71 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 114
  (Polychromatic418967fa.accept_14_8_1_2_1_965 8 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 114 (accept_3_4 7 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  114 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 71 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 114 (accept_3_4 4 71 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 71 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 114 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 71
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 114 (accept_3_4 1 71 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71 114)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45
  70 114 (Eq.refl Bool.true) (allA_succ_of_gcd 44 70 114 2 22 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 114 (Polychromatic418967fa.accept_13_4_5_10_1_1247 43 70 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 114 2 21 35 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 114 (accept_3_5 41
  70 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 114 2 20 35 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 70 114
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 70 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 70 114 2 19 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 70 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 70 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 114 2 18 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 70 114 (accept_3_5 35 70 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 70 114 2 17 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 114 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 70 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 114 2 16 35 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 114
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 70 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 70 114 2 15 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 70 114 (accept_3_5 29 70 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70
  114 2 14 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  70 114 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 70 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 70 114 2 13 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 70 114 (Polychromatic418967fa.accept_16_9_6_2_1_3101 25 70 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 114 2 12 35 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 114 (accept_3_5 23 70 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 114 2 11 35 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 114
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 70 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 114 2 10 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 70 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 114 2 9 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 114 (accept_3_5 17 70 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 70 114 2 8 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 70 114 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 70 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 114 2 7 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 13
  70 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 114 2 6 35 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 114 (accept_3_5 11
  70 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 114 2 5 35 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 114
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 70 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 114 2 4 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 114 (Polychromatic418967fa.accept_17_7_2_12_1_1069 7 70 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 114 2 3 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 114 (accept_3_5 5 70 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 70 114 2 2 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 70 114 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 70 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 114 2 1 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 70
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  114))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 69 114 (Eq.refl Bool.true) (allA_succ_of_gcd 45 69 114
  3 15 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69
  114 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 69 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 69 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 69 114 3 14 23 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 69 114
  (Polychromatic418967fa.accept_18_5_15_6_1_3999 41 69 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 114 (Polychromatic418967fa.accept_11_7_3_4_1_729 40 69 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 114 3 13 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 38
  69 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 114
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 37 69 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 69 114 3 12 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 69 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 69 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 114 (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 69
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 114 3 11 23 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 114
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 69 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 114 3 10 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 29
  69 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 114
  (Polychromatic418967fa.accept_10_8_9_4_1_961 28 69 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 69 114 3 9 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 69 114 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 69 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 114 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 69 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 114 3 8 23 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 69 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 114 3 7 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 114 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 69 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 69 114 3 6 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 69 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 69 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 114 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 69 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 114 3 5 23 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 114
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 69 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 114 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 69 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 114 3 4 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 114
  (Polychromatic418967fa.accept_7_3_6_2_1_90 10 69 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 69 114 3 3 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 69 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 69 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 114 3 2 23 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 114
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 69 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 114 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 69 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 114 3 1 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 114 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 69 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 114
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 69 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 114)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 68 114 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 68 114 2 23 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 68 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 68 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 114 2 22 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 114 (accept_3_4 43 68 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 114 2 21 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 114 (Polychromatic418967fa.accept_13_2_3_10_1_658 41 68 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 114 2 20 34 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 114
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 68 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 114 2 19 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 68 114 (accept_3_4 37 68 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68
  114 2 18 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  68 114 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 68 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 68 114 2 17 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 68 114 (Polychromatic418967fa.accept_12_9_8_6_1_466 33 68 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 114 2 16 34 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 114 (accept_3_4 31 68 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 114 2 15 34 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 114
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 68 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 68 114 2 14 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 68 114 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 68 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 114 2 13 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 114 (accept_3_4 25 68 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 114 2 12 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 114 (Polychromatic418967fa.accept_20_3_8_14_1_5342 23 68 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 114 2 11 34 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 114
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 68 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 114 2 10 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 114 (accept_3_4 19 68 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  114 2 9 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 68 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 114 2 8 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 114 (Polychromatic418967fa.accept_12_3_8_6_1_895 15 68 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 114 2 7 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 114 (accept_3_4 13 68 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 114 2 6 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 68 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 68 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 114 2 5 34 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 114
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 68 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 114 2 4 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 114 (accept_3_4 7 68 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 114
  2 3 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  114 (Polychromatic418967fa.accept_20_5_8_14_1_5341 5 68 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 68 114 2 2 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 68 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 68 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 114 2 1 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 114 (accept_3_4 1 68 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 68 114))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 67 114 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 67 114 (accept_3_5 47 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 67 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 67 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 67 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 114 (accept_3_5 44 67 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 43
  67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 114
  (Polychromatic418967fa.accept_10_2_7_4_1_967 42 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 114 (accept_3_5 41 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 114 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 67 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 114 (accept_3_5 38 67 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 114
  (Polychromatic418967fa.accept_21_15_4_9_1_5340 36 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 114 (accept_3_5 35 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 114 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 114 (accept_3_5 32 67 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 114 (Polychromatic418967fa.accept_10_1_7_4_1_968 31 67 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 114
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 114 (accept_3_5 29 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 114 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 67 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 114 (accept_3_5 26 67 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 114
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 114 (accept_3_5 23 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 114 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 114 (accept_3_5 20 67 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 67 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 114
  (Polychromatic418967fa.accept_13_5_2_10_1_248 18 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 114 (accept_3_5 17 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 114 (Polychromatic418967fa.accept_16_15_3_2_1_4170 15 67 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 114 (accept_3_5 14 67 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 114
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 114 (accept_3_5 11 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 114 (accept_3_5 8 67 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 67 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 114
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 114 (accept_3_5 5 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  114 (Polychromatic418967fa.accept_23_4_21_22_1_5339 4 67 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 114 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 67 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 114 (accept_3_5 2 67 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 114))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 66 114 (Eq.refl Bool.true) (allA_succ_of_gcd 48 66 114 6 8 11 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 114
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 66 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 114 2 23 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 66 114 3 15 22 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 66 114 2 22 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 66 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 114 6 7 11 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 66 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 114 2 20 33 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 66 114 3 13 22 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 66 114 2 19 33 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 114
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 66 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 114 6 6 11 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 114 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 66 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 114 2 17 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 66 114 3 11 22 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 66 114 2 16 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 114 (Polychromatic418967fa.accept_9_4_3_6_1_532 31
  66 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 114 6 5 11 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 114
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 66 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 114 2 14 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 66 114 3 9 22 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 66 114 2 13 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 114 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 66 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 114 6 4 11 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 66 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 114 2 11 33 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 66 114 3 7 22 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 66 114 2 10 33 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 114
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 66 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 114 6 3 11 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 114 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 66 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 114 2 8 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 66 114 3 5 22 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 66 114 2 7 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 66 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 114 6 2 11 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 114
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 66 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 114 2 5 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 66 114 3 3 22 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 66 114 2 4 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 114 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 66 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 114 6 1 11 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 66 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 114 2 2 33 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 66 114 3 1 22 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 66 114 2 1 33 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 114
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 66 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 114))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 65 114 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 65 114 (accept_3_4 49 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  65 114 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 65 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 114 (accept_3_4 46 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 114 (Polychromatic418967fa.accept_17_11_14_12_1_2995 45 65 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 114
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 65 114 (accept_3_4 43 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 114 (Polychromatic418967fa.accept_15_12_5_9_1_3234 42 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 114 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 114 (accept_3_4 40 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 65 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 114
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 38 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 114 (accept_3_4 37 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 114 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 114 (accept_3_4 34 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 114 (Polychromatic418967fa.accept_15_3_5_9_1_764 33 65 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 114
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 114 (accept_3_4 31 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 114 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 114 (Polychromatic418967fa.accept_10_9_5_4_1_966 29 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 114 (accept_3_4 28 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 114
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 114 (accept_3_4 25 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 114 (Polychromatic418967fa.accept_21_3_2_9_1_5338 24 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 114 (accept_3_4 22 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 114 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 65 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 114
  (Polychromatic418967fa.accept_21_20_2_9_1_5337 20 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 114 (accept_3_4 19 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 114 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 114 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 114 (accept_3_4 16 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 65 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 114
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 114 (accept_3_4 13 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 114 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 114 (accept_3_4 10 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 114 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 65 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 114
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 114 (accept_3_4 7 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  114 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 114 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 65 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 114 (accept_3_4 4 65 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 114 (Polychromatic418967fa.accept_22_2_21_4_1_3792
  2 65 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 114 (accept_3_4 1 65
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65 114))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 64 114 (Eq.refl Bool.true) (allA_succ_of_gcd 50 64 114 2 25 32 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 114
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 64 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 114 2 24 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 114 (accept_3_5 47 64 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  114 2 23 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  64 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 64 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 114 2 22 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 64 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 114 2 21 32 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 114 (accept_3_5 41 64 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 114 2 20 32 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 114
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 64 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 64 114 2 19 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 64 114 (Polychromatic418967fa.accept_13_11_12_10_1_2652 37 64 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 114 2 18 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 114 (accept_3_5 35 64 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64 114 2 17 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 64 114 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 64 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 114 2 16 32 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 114
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 64 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 114 2 15 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 64 114 (accept_3_5 29 64 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64
  114 2 14 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  64 114 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 64 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 64 114 2 13 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 64 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 64 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 114 2 12 32 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 114 (accept_3_5 23 64 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 114 2 11 32 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 114
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 64 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 64 114 2 10 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 64 114 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 64 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 114 2 9 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 114 (accept_3_5 17 64 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 64 114 2 8 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 64 114 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 64 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 114 2 7 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 114 (Polychromatic418967fa.accept_7_6_1_2_1_230 13
  64 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 114 2 6 32 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 114 (accept_3_5 11
  64 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 114 2 5 32 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 114
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 64 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 64 114 2 4 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 64 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 64 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 114 2 3 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 114 (accept_3_5 5 64 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 64 114 2 2 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 64 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 64 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 114 2 1 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 114 (Polychromatic418967fa.accept_14_1_8_2_1_1675 1
  64 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  114))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 63 114 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  63 114 3 17 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  50 63 114 (Polychromatic418967fa.accept_12_2_3_6_1_112 50 63 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 63 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 63 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 63 114 3 16 21 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 114
  (Polychromatic418967fa.accept_10_7_3_4_1_978 47 63 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 114 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 63 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 114 3 15 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 114 (Polychromatic418967fa.accept_12_8_3_6_1_909 44
  63 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 114
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 43 63 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 63 114 3 14 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 63 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 114 (Polychromatic418967fa.accept_11_7_8_4_1_718 40 63 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 114 3 13 21 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 114
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 63 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 114 3 12 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 114 (Polychromatic418967fa.accept_15_5_3_9_1_283 35
  63 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 114
  (Polychromatic418967fa.accept_11_1_8_4_1_717 34 63 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 63 114 3 11 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 63 114 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 63 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 114 (Polychromatic418967fa.accept_18_13_9_6_1_4024 31 63
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 114 3 10 21 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 63 114 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 63 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 114 3 9 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 114 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 63 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 63 114 3 8 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 63 114 (Polychromatic418967fa.accept_11_1_8_4_1_717 23 63 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 114 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 63 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 114 3 7 21 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 114
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 63 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 114 (Polychromatic418967fa.accept_10_9_3_4_1_985 19 63 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 114 3 6 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 114
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 63 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 63 114 3 5 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 63 114 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 63 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 114 3 4 21 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 114
  (Polychromatic418967fa.accept_20_11_3_14_1_5336 11 63 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 114 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 63 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 114 3 3 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 114 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 63 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 114
  (Polychromatic418967fa.accept_10_7_3_4_1_978 7 63 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 63 114 3 2 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 63 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 114 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 63 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 114 3 1 21 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 114
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 63 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 63 114)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 62
  114 (Eq.refl Bool.true) (allA_succ_of_gcd 52 62 114 2 26 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 114 (Polychromatic418967fa.accept_12_3_2_6_1_138 51 62 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 62 114 2 25 31 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 62 114 (accept_3_4 49
  62 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62 114 2 24 31 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 62 114
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 62 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 62 114 2 23 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 62 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 62 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 114 2 22 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 114 (accept_3_4 43 62 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 114 2 21 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 114 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 62 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 114 2 20 31 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 114
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 62 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 114 2 19 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 62 114 (accept_3_4 37 62 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62
  114 2 18 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  62 114 (Polychromatic418967fa.accept_21_14_20_9_1_5306 35 62 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 62 114 2 17 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 62 114 (Polychromatic418967fa.accept_12_9_2_6_1_455 33 62 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 62 114 2 16 31 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 62 114 (accept_3_4 31 62 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62 114 2 15 31 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 62 114
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 62 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 62 114 2 14 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 62 114 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 62 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 114 2 13 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 114 (accept_3_4 25 62 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 114 2 12 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 114 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 62 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 114 2 11 31 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 114
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 62 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 114 2 10 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 62 114 (accept_3_4 19 62 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62
  114 2 9 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  62 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 62 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 62 114 2 8 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 62 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 62 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 114 2 7 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 114 (accept_3_4 13 62 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 114 2 6 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 62 114 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 62 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 62 114 2 5 31 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 62 114
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 62 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 62 114 2 4 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 62 114 (accept_3_4 7 62 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 114
  2 3 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 62
  114 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 62 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 62 114 2 2 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 62 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 62 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 114 2 1 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 114 (accept_3_4 1 62 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 114))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 61 114 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 61 114 (accept_3_5 53 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 61 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 61 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 61 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 114 (accept_3_5 50 61 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 49
  61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 114
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 114 (accept_3_5 47 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 61 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 114 (accept_3_5 44 61 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 114
  (Polychromatic418967fa.accept_17_8_10_12_1_5335 42 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 114 (accept_3_5 41 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 114 (accept_3_5 38 61 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 61 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 114
  (Polychromatic418967fa.accept_15_6_1_9_1_1476 36 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 114 (accept_3_5 35 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 114 (Polychromatic418967fa.accept_23_11_15_22_1_5334 34 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 114 (Polychromatic418967fa.accept_20_13_1_14_1_5333 33 61 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 114 (accept_3_5 32 61 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 114
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 114 (accept_3_5 29 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 114 (accept_3_5 26 61 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 61 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 114
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 114 (accept_3_5 23 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 114 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 61 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 114 (accept_3_5 20 61 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 114
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 114 (accept_3_5 17 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 114 (Polychromatic418967fa.accept_23_16_15_22_1_5332 16 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 114 (accept_3_5 14 61 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 61 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 114
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 114 (accept_3_5 11 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 114 (Polychromatic418967fa.accept_18_9_7_6_1_5331 9 61 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 114 (accept_3_5 8 61 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 114
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 6 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 114 (accept_3_5 5 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  114 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 61 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 114 (accept_3_5 2 61 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 61 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 114))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 60 114 (Eq.refl Bool.true) (allA_succ_of_gcd 54 60 114 6 9 10 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 114
  (Polychromatic418967fa.accept_21_11_18_9_1_465 53 60 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 60 114 2 26 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 60 114 3 17 20 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 60 114 2 25 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 114 (Polychromatic418967fa.accept_16_1_12_2_1_2136 49 60 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 114 6 8 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 60 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 114 2 23 30 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 114 3 15 20 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 114 2 22 30 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 114
  (Polychromatic418967fa.accept_11_10_5_4_1_711 43 60 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 114 6 7 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 114 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 60 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 114 2 20 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 60 114 3 13 20 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 60 114 2 19 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 114 (Polychromatic418967fa.accept_13_11_8_10_1_676
  37 60 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 114 6 6 10 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 114
  (Polychromatic418967fa.accept_21_14_18_9_1_5330 35 60 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 60 114 2 17 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 60 114 3 11 20 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 60 114 2 16 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 114 (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 60 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 114 6 5 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 114 (Polychromatic418967fa.accept_21_8_18_9_1_5329 29 60 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 114 2 14 30 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 60 114 3 9 20 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 60 114 2 13 30 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 114
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 25 60 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 114 6 4 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 60 114 (Polychromatic418967fa.accept_14_9_4_2_1_983 23 60 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 114 2 11 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 60 114 3 7 20 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 114 2 10 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 19
  60 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 114 6 3 10 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 114
  (Polychromatic418967fa.accept_13_4_8_10_1_671 17 60 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 60 114 2 8 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 60 114 3 5 20 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 60 114 2 7 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 60 114 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 60 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 114 6 2 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 114 (Polychromatic418967fa.accept_13_11_8_10_1_676 11 60 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 114 2 5 30 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 114 3 3 20 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 60 114 2 4 30 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 114
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 60 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 114 6 1 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 60 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 114 2 2 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 114 3 1 20 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 114 2 1 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 114 (Polychromatic418967fa.accept_16_1_12_2_1_2136 1 60 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  114))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 59 114 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 59 114 (accept_3_4 55 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  59 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 59 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 114 (accept_3_4 52 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 114 (Polychromatic418967fa.accept_13_12_7_10_1_2662 51 59 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 114
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 114 (accept_3_4 49 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 114 (accept_3_4 46 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 114
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 114 (accept_3_4 43 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 114 (Polychromatic418967fa.accept_13_3_7_10_1_668 42 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 114 (accept_3_4 40 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 59 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 114
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 114 (accept_3_4 37 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 114 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 114 (accept_3_4 34 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 114
  (Polychromatic418967fa.accept_22_10_15_4_1_5328 32 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 114 (accept_3_4 31 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 114 (accept_3_4 28 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 59 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 114
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 114 (accept_3_4 25 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 114 (Polychromatic418967fa.accept_20_4_19_14_1_5327 24 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 114 (Polychromatic418967fa.accept_10_3_9_4_1_960 23 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 114 (accept_3_4 22 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 114
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 114 (accept_3_4 19 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 114 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 114 (accept_3_4 16 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 59 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 114
  (Polychromatic418967fa.accept_21_14_17_9_1_5326 14 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 114 (accept_3_4 13 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 114 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 114 (accept_3_4 10 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 114
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 114 (accept_3_4 7 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  114 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 114 (accept_3_4 4 59 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 59 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 114 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  59 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 114 (accept_3_4 1 59 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 114))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 58 114 (Eq.refl Bool.true) (allA_succ_of_gcd 56 58 114 2 28 29 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 58 114
  (Polychromatic418967fa.accept_9_1_4_6_1_5 55 58 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 58 114 2 27 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 58 114 (accept_3_5 53 58 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58
  114 2 26 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  58 114 (Polychromatic418967fa.accept_11_7_3_4_1_729 51 58 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 58 114 2 25 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 58 114 (Polychromatic418967fa.accept_10_9_8_4_1_970 49 58 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 58 114 2 24 29 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 58 114 (accept_3_5 47 58 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58 114 2 23 29 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 58 114
  (Polychromatic418967fa.accept_12_9_10_6_1_872 45 58 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 58 114 2 22 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 58 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 58 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 114 2 21 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 114 (accept_3_5 41 58 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 114 2 20 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 114 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 58 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 58 114 2 19 29 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 58 114
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 58 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 58 114 2 18 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 58 114 (accept_3_5 35 58 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58
  114 2 17 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  58 114 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 58 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 58 114 2 16 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 58 114 (Polychromatic418967fa.accept_13_5_6_10_1_2659 31 58 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 58 114 2 15 29 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 58 114 (accept_3_5 29 58 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58 114 2 14 29 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 58 114
  (Polychromatic418967fa.accept_12_3_10_6_1_442 27 58 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 58 114 2 13 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 58 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 58 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 114 2 12 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 114 (accept_3_5 23 58 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 114 2 11 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 114 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 58 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 114 2 10 29 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 114
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 58 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 114 2 9 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 114 (accept_3_5 17 58 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58
  114 2 8 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  58 114 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 58 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 58 114 2 7 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 58 114 (Polychromatic418967fa.accept_21_13_16_9_1_2541 13 58 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 114 2 6 29 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 114 (accept_3_5 11 58 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 114 2 5 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 114 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 58 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 58 114 2 4 29 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 58 114
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 58 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 58 114 2 3 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 58 114 (accept_3_5 5 58 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 114
  2 2 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 58
  114 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 58 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 58 114 2 1 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 58 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 58 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 58 114))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  57 114 (allA_succ_of_accept 56 57 114 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 57 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 114 3 18 19 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 114
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 57 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 57 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 57 114 3 17 19 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 57 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 50
  57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 114
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 57 114 3 16 19 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 57 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 57 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 114 3 15 19 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 114
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 57 114 3 14 19 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 57 114 (Polychromatic418967fa.accept_7_6_1_2_1_230 41
  57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 114
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 57 114 3 13 19 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 57 114 19 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 57 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 57 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 114 3 12 19 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 114
  (Polychromatic418967fa.accept_7_6_1_2_1_230 34 57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 114 3 11 19 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 57 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 114 3 10 19 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 114
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 57 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 114 3 9 19 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 114 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 57 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 114
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 114 3 8 19 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 114 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 57 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 114 3 7 19 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 114
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 19 57 114 19 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 57 114 3 6 19 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 57 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 57 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 114 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 57 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 114 3 5 19 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 114
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 114 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 57 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 114 3 4 19 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 114
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 57 114 3 3 19 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 57 114 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 114 3 2 19 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 114
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 114 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 57 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 114 3 1 19 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 114 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 57 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 114
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 114))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 114 (allA_succ_of_accept 55 56
  114 (accept_3_4 55 56 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 56 114 2 27 28 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 56 114
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 56 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 56 114 2 26 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 56 114 (Polychromatic418967fa.accept_12_3_8_6_1_895 51 56 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 114 2 25 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 114 (accept_3_4 49 56 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 114 2 24 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 114 (Polychromatic418967fa.accept_13_8_4_10_1_4358 47 56 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 114 2 23 28 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 114
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 56 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 56 114 2 22 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 56 114 (accept_3_4 43 56 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56
  114 2 21 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  56 114 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 56 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 56 114 2 20 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 56 114 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 56 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 114 2 19 28 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 114 (accept_3_4 37 56 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 114 2 18 28 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 56 114
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 56 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 56 114 2 17 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 56 114 (Polychromatic418967fa.accept_12_9_8_6_1_466 33 56 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 114 2 16 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 114 (accept_3_4 31 56 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 114 2 15 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 114 (Polychromatic418967fa.accept_31_29_25_21_1_5325 29 56
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 114 2 14 28 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 114
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 56 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 56 114 2 13 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 56 114 (accept_3_4 25 56 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56
  114 2 12 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  56 114 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 56 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 56 114 2 11 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 56 114 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 56 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 114 2 10 28 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 114 (accept_3_4 19 56 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 114 2 9 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 56 114 (Polychromatic418967fa.accept_9_8_2_6_1_875 17
  56 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 114 2 8 28 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 114
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 56 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 56 114 2 7 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 56 114 (accept_3_4 13 56 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56
  114 2 6 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  56 114 (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 56 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 56 114 2 5 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 114 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 56 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 114 2 4 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 114 (accept_3_4 7 56 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 114 2 3 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 56 114 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 56 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 114 2 2 28 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 114
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 56 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 56 114 2 1 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 56 114 (accept_3_4 1 56 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  114)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 114 (allA_succ_of_accept 54 55 114
  (Polychromatic418967fa.accept_13_2_3_10_1_658 54 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 114 (accept_3_5 53 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 114 (Polychromatic418967fa.accept_10_1_5_4_1_276 51 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 114 (accept_3_5 50 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 55 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 114
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 114 (accept_3_5 47 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 114 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 114 (accept_3_5 44 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 55 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 114
  (Polychromatic418967fa.accept_15_12_10_9_1_798 42 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 114 (accept_3_5 41 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 114 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 114 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 114 (accept_3_5 38 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 114
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 114 (accept_3_5 35 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 114 (accept_3_5 32 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 55 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 114
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 114 (accept_3_5 29 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 114 (Polychromatic418967fa.accept_13_2_3_10_1_658 28 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 114 (Polychromatic418967fa.accept_15_12_10_9_1_798 27 55 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 114 (accept_3_5 26 55 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 114
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 114 (accept_3_5 23 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 114 (accept_3_5 20 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 114 (Polychromatic418967fa.accept_10_9_5_4_1_966 19 55 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 114
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 114 (accept_3_5 17 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 114 (accept_3_5 14 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 114
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 114 (accept_3_5 11 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 114 (accept_3_5 8 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 55 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 114
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 114 (accept_3_5 5 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  114 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 55 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 55 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 114 (accept_3_5 2 55 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 114)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 114 (allA_succ_of_accept 53 54 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 54 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 114 2 26 27 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 54 114 3 17 18 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 54 114 2 25 27 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 114
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 49 54 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 114 6 8 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 54 114 (Polychromatic418967fa.accept_13_8_2_10_1_652 47 54 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 114 2 23 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 54 114 3 15 18 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 54 114 2 22 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 114 (Polychromatic418967fa.accept_16_11_6_2_1_4155
  43 54 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 114 6 7 9 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 114
  (Polychromatic418967fa.accept_16_9_6_2_1_3101 41 54 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 54 114 2 20 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 54 114 3 13 18 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 54 114 2 19 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 54 114 (Polychromatic418967fa.accept_13_11_2_10_1_4399 37 54 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 114 6 6 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 114 (Polychromatic418967fa.accept_14_7_12_2_1_2502 35 54 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 114 2 17 27 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 54 114 3 11 18 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 54 114 2 16 27 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 114
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 54 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 114 6 5 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 114 (Polychromatic418967fa.accept_13_3_2_10_1_2697 29 54 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 114 2 14 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 54 114 3 9 18 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 54 114 2 13 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 25
  54 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 114 6 4 9 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 114
  (Polychromatic418967fa.accept_21_2_12_9_1_5324 23 54 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 114 2 11 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 54 114 3 7 18 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 54 114 2 10 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 54 114 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 54 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 114 6 3 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 54 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 114 2 8 27 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 54 114 3 5 18 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 54 114 2 7 27 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 114
  (Polychromatic418967fa.accept_21_13_12_9_1_5323 13 54 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 114 6 2 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 54 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 114 2 5 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 114 3 3 18 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 54 114 2 4 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 114 (Polychromatic418967fa.accept_14_7_12_2_1_2502 7 54 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 114 6 1 9 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 114
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 54 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 54 114 2 2 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 54 114 3 1 18 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 54 114 2 1 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 114 (Polychromatic418967fa.accept_16_1_6_2_1_3100 1 54 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 114)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  114 (allA_succ_of_accept 52 53 114 (accept_3_4 52 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 53 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 114 (Polychromatic418967fa.accept_9_5_8_6_1_281 50 53 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 114 (accept_3_4 49 53 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 114 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 53 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 114 (accept_3_4 46 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 114 (Polychromatic418967fa.accept_16_13_5_2_1_2131 45 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 114 (Polychromatic418967fa.accept_15_14_8_9_1_1452 44 53 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 114 (accept_3_4 43 53 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 114 (Polychromatic418967fa.accept_22_20_9_4_1_5322 42 53
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 114
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 114 (accept_3_4 40 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 114 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 53 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 114 (accept_3_4 37 53 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 114 (Polychromatic418967fa.accept_21_15_11_9_1_2470 36 53 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 114 (accept_3_4 34 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 114 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 53 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 114 (accept_3_4 31 53 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 53 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 114
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 114 (accept_3_4 28 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 53 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 114 (accept_3_4 25 53 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 114 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 53 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 114 (accept_3_4 22 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 114 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 53 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 114 (accept_3_4 19 53 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 114 (Polychromatic418967fa.accept_15_3_8_9_1_795 18 53 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 114
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 114 (accept_3_4 16 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 114 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 53 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 114 (accept_3_4 13 53 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 53 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 114 (accept_3_4 10 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 114 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 114 (Polychromatic418967fa.accept_20_8_13_14_1_5321 8 53 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 114 (accept_3_4 7 53 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 114 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 53 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 114
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 114 (accept_3_4 4 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 114 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 53 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 114 (accept_3_4 1 53 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 114))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 114
  (allA_succ_of_accept 51 52 114 (Polychromatic418967fa.accept_11_7_8_4_1_718 51 52 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 114 2 25 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 49
  52 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 114 2 24 26 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 114 (accept_3_5 47
  52 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 114 2 23 26 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 114
  (Polychromatic418967fa.accept_11_1_8_4_1_717 45 52 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 52 114 2 22 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 52 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 52 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 114 2 21 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 114 (accept_3_5 41 52 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 114 2 20 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 114 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 52 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 52 114 2 19 26 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 52 114
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 52 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 52 114 2 18 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 52 114 (accept_3_5 35 52 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52
  114 2 17 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  52 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 52 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 52 114 2 16 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 52 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 52 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 114 2 15 26 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 114 (accept_3_5 29 52 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 114 2 14 26 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 114
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 52 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 52 114 2 13 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 52 114 (Polychromatic418967fa.accept_29_25_23_27_1_5320 25 52 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 114 2 12 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 114 (accept_3_5 23 52 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 114 2 11 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 114 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 52 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 114 2 10 26 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 114
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 52 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 114 2 9 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 114 (accept_3_5 17 52 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  114 2 8 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 52 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 114 2 7 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 52 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 52 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 114 2 6 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 114 (accept_3_5 11 52 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 114 2 5 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 52 114 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 52 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 114 2 4 26 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 114
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 52 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 52 114 2 3 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 52 114 (accept_3_5 5 52 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 114
  2 2 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52
  114 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 52 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 52 114 2 1 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 52 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 52 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 52 114)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 114
  (allA_succ_of_accept 50 51 114 (Polychromatic418967fa.accept_12_2_3_6_1_112 50 51 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 114 3 16 17 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 114
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 47 51 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 51 114 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 51 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 51 114 3 15 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 51 114 (Polychromatic418967fa.accept_12_8_3_6_1_909 44
  51 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 114
  (Polychromatic418967fa.accept_20_3_11_14_1_5319 43 51 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 51 114 3 14 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 51 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 114 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 51 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 114 3 13 17 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 114
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 51 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 114 3 12 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 114 (Polychromatic418967fa.accept_10_5_1_4_1_1444
  35 51 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 114
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 51 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 51 114 3 11 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 51 114 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 51 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 114 (Polychromatic418967fa.accept_15_1_6_9_1_254 31 51 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 114 3 10 17 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 114 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 51 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 114 3 9 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 114 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 51 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 51 114 3 8 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 51 114 (Polychromatic418967fa.accept_18_5_15_6_1_3999 23 51 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 114 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 51 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 114 3 7 17 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 114
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 51 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 114 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 51 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 114 3 6 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 114
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 51 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 51 114 3 5 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 51 114 (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 51 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 114 3 4 17 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 114
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 51 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 51 114 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 51 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 114 3 3 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 114 (Polychromatic418967fa.accept_11_8_7_4_1_3011 8
  51 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 114
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 51 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 51 114 3 2 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 51 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 114 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 51 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 114 3 1 17 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 114
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 51 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 51 114))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 114
  (allA_succ_of_accept 49 50 114 (accept_3_4 49 50 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50
  114 2 24 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  50 114 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 50 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 50 114 2 23 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 50 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 50 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 114 2 22 25 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 114 (accept_3_4 43 50 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 114 2 21 25 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 114
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 50 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 114 2 20 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 50 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 114 2 19 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 114 (accept_3_4 37 50 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 114 2 18 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 114 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 50 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 114 2 17 25 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 114
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 50 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 114 2 16 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 50 114 (accept_3_4 31 50 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50
  114 2 15 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  50 114 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 50 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 50 114 2 14 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 50 114 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 50 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 114 2 13 25 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 114 (accept_3_4 25 50 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 114 2 12 25 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 114
  (Polychromatic418967fa.accept_24_23_2_18_1_5318 23 50 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 114 2 11 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 50 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 114 2 10 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 114 (accept_3_4 19 50 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 114 2 9 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 50 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 50 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 114 2 8 25 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 114
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 50 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 50 114 2 7 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 50 114 (accept_3_4 13 50 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50
  114 2 6 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  50 114 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 50 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 114 2 5 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 50 114 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 50 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 114 2 4 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 114 (accept_3_4 7 50 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 114 2 3 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 50 114 (Polychromatic418967fa.accept_20_5_10_14_1_5317 5 50 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 114 2 2 25 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 114
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 50 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 114 2 1 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 114 (accept_3_4 1 50 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  114)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 114 (allA_succ_of_accept 48 49 114
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 49 114 (accept_3_5 47 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  49 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 49 114 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 114 (accept_3_5 44 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 49 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 114
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 42 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 114 (accept_3_5 41 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 114 (Polychromatic418967fa.accept_14_12_7_2_1_1663 40 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 114 (accept_3_5 38 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 49 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 114
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 36 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 114 (accept_3_5 35 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 114 (Polychromatic418967fa.accept_10_3_9_4_1_960 33 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 114 (accept_3_5 32 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 114
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 114 (accept_3_5 29 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 114 (accept_3_5 26 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 114
  (Polychromatic418967fa.accept_20_4_9_14_1_5316 24 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 114 (accept_3_5 23 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 114 (Polychromatic418967fa.accept_16_6_1_2_1_3129 22 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 114 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 114 (accept_3_5 20 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 114
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 114 (accept_3_5 17 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 114 (accept_3_5 14 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 114 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 49 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 114
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 114 (accept_3_5 11 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 114 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 114 (accept_3_5 8 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 114
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 6 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 114 (accept_3_5 5 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  114 (Polychromatic418967fa.accept_20_4_9_14_1_5316 4 49 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 114 (accept_3_5 2 49 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 114)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 114 (allA_succ_of_accept 47 48 114 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 48 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 114 2 23 24 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 48 114 3 15 16 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 48 114 2 22 24 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 114
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 48 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 114 6 7 8 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 48 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 114 2 20 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 48 114 3 13 16 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 48 114 2 19 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  48 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 114 6 6 8 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 114
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 48 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 114 2 17 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 48 114 3 11 16 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 48 114 2 16 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 48 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 114 6 5 8 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 48 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 114 2 14 24 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 48 114 3 9 16 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 48 114 2 13 24 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 114
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 48 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 114 6 4 8 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 48 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 114 2 11 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 48 114 3 7 16 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 48 114 2 10 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 19
  48 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 114 6 3 8 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 114
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 48 114 2 8 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 48 114 3 5 16 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 48 114 2 7 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 114 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 114 6 2 8 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 114 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 114 2 5 24 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 48 114 3 3 16 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 48 114 2 4 24 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 114
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 114 6 1 8 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 48 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 114 2 2 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 114 3 1 16 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 114 2 1 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 48 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  114)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 114 (allA_succ_of_accept 46 47 114 (accept_3_4 46 47
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 114 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 114
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 47 114 (accept_3_4 43 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  47 114 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 47 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 114 (accept_3_4 40 47 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 47 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 114
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 114 (accept_3_4 37 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 114 (Polychromatic418967fa.accept_21_15_5_9_1_5315 36 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 114 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 47 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 114 (accept_3_4 34 47 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 114
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 114 (accept_3_4 31 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 114 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 114 (accept_3_4 28 47 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 114 (Polychromatic418967fa.accept_25_2_22_14_1_5314 27 47 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 114
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 114 (accept_3_4 25 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 114 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 47 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 114 (accept_3_4 22 47 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 114
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 20 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 114 (accept_3_4 19 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 114 (accept_3_4 16 47 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 114 (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 47 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 114
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 114 (accept_3_4 13 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 114 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 47 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 114 (accept_3_4 10 47 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 114
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 114 (accept_3_4 7 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  114 (Polychromatic418967fa.accept_23_6_1_22_1_5313 6 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 47 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 114 (accept_3_4 4 47 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 47 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 114
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 114 (accept_3_4 1 47 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  114))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 114 (allA_succ_of_accept 45 46 114
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 46 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 114 2 22 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 46 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 46 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 114 2 21 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 114 (accept_3_5 41 46 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 114 2 20 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 114 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 46 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 114 2 19 23 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 114
  (Polychromatic418967fa.accept_14_9_4_2_1_983 37 46 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 114 2 18 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 114 (accept_3_5 35 46 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46
  114 2 17 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  46 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 46 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 46 114 2 16 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 46 114 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 46 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 114 2 15 23 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 114 (accept_3_5 29 46 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 114 2 14 23 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 114
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 46 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 46 114 2 13 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 46 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 46 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 114 2 12 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 114 (accept_3_5 23 46 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 114 2 11 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 114 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 46 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 114 2 10 23 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 114
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 46 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 114 2 9 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 114 (accept_3_5 17 46 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  114 2 8 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 114 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 46 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 114 2 7 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 46 114 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 46 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 114 2 6 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 114 (accept_3_5 11 46 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 114 2 5 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 46 114 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 46 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 114 2 4 23 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 114
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 46 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 46 114 2 3 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 46 114 (accept_3_5 5 46 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 114
  2 2 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46
  114 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 46 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 46 114 2 1 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 46 114 (Polychromatic418967fa.accept_20_1_6_14_1_5312 1 46 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 46 114)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 114
  (allA_succ_of_accept 44 45 114 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 45 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 45 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 114 3 14 15 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 114
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 45 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 45 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 45 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 45 114 3 13 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 114 (Polychromatic418967fa.accept_12_2_9_6_1_439 38
  45 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 114
  (Polychromatic418967fa.accept_16_5_13_2_1_2138 37 45 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 45 114 3 12 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 45 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 45 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 45 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 114 3 11 15 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 114
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 45 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 114 3 10 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 29
  45 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 114
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 45 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 45 114 3 9 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 45 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 114 (Polychromatic418967fa.accept_13_12_6_10_1_667 25 45
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 114 3 8 15 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 45 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 114 3 7 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 45 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 45 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 45 114 3 6 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 45 114 (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 45 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 114 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 45 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 114 3 5 15 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 114
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 45 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 45 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 114 3 4 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 114
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 45 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 45 114 3 3 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 45 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 114 3 2 15 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 114
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 45 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 45 114 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 45 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 114 3 1 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 114 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 45 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 114
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 45 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 114))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 114 (allA_succ_of_accept 43 44 114
  (accept_3_4 43 44 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 114 2 21 22 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 114
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 44 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 114 2 20 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 44 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 44 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 114 2 19 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 114 (accept_3_4 37 44 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 114 2 18 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 114 (Polychromatic418967fa.accept_15_5_14_9_1_274 35 44 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 114 2 17 22 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 114
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 44 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 114 2 16 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 114 (accept_3_4 31 44 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  114 2 15 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 114 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 44 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 114 2 14 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 44 114 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 44 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 114 2 13 22 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 114 (accept_3_4 25 44 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 114 2 12 22 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 114
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 44 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 44 114 2 11 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 44 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 44 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 114 2 10 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 114 (accept_3_4 19 44 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 114 2 9 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 44 114 (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 44 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 114 2 8 22 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 114
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 44 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 114 2 7 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 114 (accept_3_4 13 44 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44
  114 2 6 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  44 114 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 44 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 114 2 5 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 44 114 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 44 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 114 2 4 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 114 (accept_3_4 7 44 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 114 2 3 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 44 114 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 44 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 114 2 2 22 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 114
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 44 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 114 2 1 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 114 (accept_3_4 1 44 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  114)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 114 (allA_succ_of_accept 42 43 114
  (Polychromatic418967fa.accept_22_20_21_4_1_5311 42 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 114 (accept_3_5 41 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 114 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 43 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 114 (accept_3_5 38 43 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 114
  (Polychromatic418967fa.accept_14_8_1_2_1_965 36 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 114 (accept_3_5 35 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 114 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 114 (accept_3_5 32 43 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 43 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 114
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 114 (accept_3_5 29 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 114 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 43 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 114 (accept_3_5 26 43 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 114
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 114 (accept_3_5 23 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 114 (accept_3_5 20 43 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 43 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 114
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 114 (accept_3_5 17 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 114 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 114 (Polychromatic418967fa.accept_22_15_21_4_1_5310 15 43 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 114 (accept_3_5 14 43 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 114
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 114 (accept_3_5 11 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 114 (accept_3_5 8 43 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 114 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 43 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 114
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 114 (accept_3_5 5 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  114 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 43 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 43 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 114 (accept_3_5 2 43 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 114))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 114
  (allA_succ_of_accept 41 42 114 (Polychromatic418967fa.accept_13_2_3_10_1_658 41 42 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 114 2 20 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 42 114 3 13 14 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 42 114 2 19 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 114 (Polychromatic418967fa.accept_10_7_2_4_1_569 37
  42 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 114 6 6 7 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 114
  (Polychromatic418967fa.accept_11_2_9_4_1_310 35 42 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 42 114 2 17 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 42 114 3 11 14 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 42 114 2 16 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 114 (Polychromatic418967fa.accept_22_9_20_4_1_5309 31 42 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 114 6 5 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 114 (Polychromatic418967fa.accept_15_14_12_9_1_3216 29 42
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 114 2 14 21 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 114 3 9 14 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 42 114 2 13 21 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 114
  (Polychromatic418967fa.accept_15_10_12_9_1_776 25 42 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 114 6 4 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 114 (Polychromatic418967fa.accept_27_23_15_6_1_5308 23 42 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 114 2 11 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 114 3 7 14 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 114 2 10 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 114 (Polychromatic418967fa.accept_13_6_3_10_1_698
  19 42 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 114 6 3 7 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 114
  (Polychromatic418967fa.accept_10_7_2_4_1_569 17 42 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 114 2 8 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 42 114 3 5 14 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 42 114 2 7 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 114 (Polychromatic418967fa.accept_11_2_9_4_1_310 13 42 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 114 6 2 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 114 (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 42
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 114 2 5 21 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 114 3 3 14 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 114 2 4 21 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 114
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 42 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 114 6 1 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 114 (Polychromatic418967fa.accept_15_5_12_9_1_2253 5 42 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 114 2 2 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 42 114 3 1 14 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 42 114 2 1 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 114 (Polychromatic418967fa.accept_25_1_17_14_1_5307 1 42 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  114)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 114 (allA_succ_of_accept 40 41 114 (accept_3_4 40 41 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  41 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 114
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 114 (accept_3_4 37 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 41 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 114 (accept_3_4 34 41 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 114 (Polychromatic418967fa.accept_16_1_9_2_1_4161 33 41 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 114
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 114 (accept_3_4 31 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 41 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 114 (accept_3_4 28 41 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 114
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 114 (accept_3_4 25 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 114 (accept_3_4 22 41 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 41 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 114
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 114 (accept_3_4 19 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 114 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 41 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 114 (accept_3_4 16 41 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 114
  (Polychromatic418967fa.accept_21_14_20_9_1_5306 14 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 114 (accept_3_4 13 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 114 (accept_3_4 10 41 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 114 (Polychromatic418967fa.accept_30_9_11_24_1_5305 9 41 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 114
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 114 (accept_3_4 7 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  114 (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 41 114 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 41 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 114 (accept_3_4 4 41 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 114
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 41 114 (accept_3_4 1 41 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41
  114))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 114 (allA_succ_of_accept 39 40 114
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 40 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 114 2 19 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 40 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 114 2 18 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 114 (accept_3_5 35 40 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 114 2 17 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 114 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 40 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 114 2 16 20 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 114
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 40 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 114 2 15 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 114 (accept_3_5 29 40 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  114 2 14 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 114 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 40 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 114 2 13 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 40 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 40 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 114 2 12 20 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 114 (accept_3_5 23 40 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 114 2 11 20 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 114
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 114 2 10 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 40 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 114 2 9 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 114 (accept_3_5 17 40 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 114 2 8 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 40 114 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 40 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 114 2 7 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 114
  (Polychromatic418967fa.accept_25_13_15_14_1_5304 13 40 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 40 114 2 6 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 40 114 (accept_3_5 11 40 114 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 40 114 2 5 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 40 114 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 40 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 114 2 4 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 40 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 114 2 3 20 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 114 (accept_3_5 5 40 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 114 2 2 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 40
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 114 2 1 20 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 114
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 40 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 114)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 114 (allA_succ_of_accept 38 39 114
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 39 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 39 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 114 3 12 13 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 114 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  39 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 114
  (Polychromatic418967fa.accept_7_6_4_2_1_236 34 39 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 114 3 11 13 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 39 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 114 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 39 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 114 3 10 13 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 39 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 114 3 9 13 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 39 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 114 3 8 13 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 39 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 114 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 39 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 114 3 7 13 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 114
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 39 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 39 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 114 3 6 13 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 114
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 39 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 114 3 5 13 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 39 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 114 3 4 13 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 114
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 39 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 39 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 114 3 3 13 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 114 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 39 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 114
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 114 3 2 13 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 114 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 39 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 114 3 1 13 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 114
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 39 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 114))))))))))))))))))))))))))))))))))))))) (allB_succ 38 114
  (allA_succ_of_accept 37 38 114 (accept_3_4 37 38 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  114 2 18 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 114 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 38 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 114 2 17 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 38 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 114 2 16 19 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 114 (accept_3_4 31 38 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 114 2 15 19 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 114
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 38 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 114 2 14 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 38 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 114 2 13 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 114 (accept_3_4 25 38 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 114 2 12 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 114 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 38 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 114 2 11 19 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 114
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 38 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 114 2 10 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 19 38 114 19 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 38 114 2 9 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 38 114 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 38 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 114 2 8 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 38 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 114 2 7 19 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 114 (accept_3_4 13 38 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 114 2 6 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 114
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 38 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 38 114 2 5 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 38 114 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 38 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 114 2 4 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 114 (accept_3_4 7 38 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 114 2 3 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 38 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 38 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 114 2 2 19 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 114
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 38 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 38 114 2 1 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 38 114 (accept_3_4 1 38 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38
  114)))))))))))))))))))))))))))))))))))))) (allB_succ 37 114 (allA_succ_of_accept 36 37 114
  (Polychromatic418967fa.accept_21_15_16_9_1_5303 36 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 114 (accept_3_5 35 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 114 (Polychromatic418967fa.accept_10_3_7_4_1_584 33 37 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 114 (accept_3_5 32 37 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 114
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 114 (accept_3_5 29 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 114 (Polychromatic418967fa.accept_13_2_11_10_1_1881 28 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 114 (accept_3_5 26 37 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 37 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 114
  (Polychromatic418967fa.accept_17_7_3_12_1_4098 24 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 114 (accept_3_5 23 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 114 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 114 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 37 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 114 (accept_3_5 20 37 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 114
  (Polychromatic418967fa.accept_14_4_9_2_1_95 18 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 114 (accept_3_5 17 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 114 (accept_3_5 14 37 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 114 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 37 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 114
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 114 (accept_3_5 11 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 114 (Polychromatic418967fa.accept_21_10_16_9_1_5302 10 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 114 (Polychromatic418967fa.accept_18_9_1_6_1_5301 9 37 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 114 (accept_3_5 8 37 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 114
  (Polychromatic418967fa.accept_21_6_16_9_1_5300 6 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 114 (accept_3_5 5 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  114 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 37 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 114 (accept_3_5 2 37 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 114 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 37 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 114))))))))))))))))))))))))))))))))))))) (allB_succ 36 114
  (allA_succ_of_accept 35 36 114 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 36 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 114 2 17 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 36 114 3 11 12 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 36 114 2 16 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 31
  36 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 114 6 5 6 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 114
  (Polychromatic418967fa.accept_11_7_3_4_1_729 29 36 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 36 114 2 14 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 36 114 3 9 12 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 36 114 2 13 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 114 (Polychromatic418967fa.accept_10_5_6_4_1_64 25 36 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 114 6 4 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 114 (Polychromatic418967fa.accept_17_6_2_12_1_1992 23 36 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 114 2 11 18 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 114 3 7 12 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 114 2 10 18 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 114
  (Polychromatic418967fa.accept_15_4_6_9_1_2269 19 36 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 114 6 3 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 36 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 114 2 8 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 114 3 5 12 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 114 2 7 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 114 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 36 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 114 6 2 6 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 114
  (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 36 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 114 2 5 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 36 114 3 3 12 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 36 114 2 4 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 114 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 36 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 114 6 1 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 114 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 36 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 114 2 2 18 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 36 114 3 1 12 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 36 114 2 1 18 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 114
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 1 36 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 114)))))))))))))))))))))))))))))))))))) (allB_succ 35 114 (allA_succ_of_accept 34 35 114 (accept_3_4 34
  35 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 35 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 114 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 35 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 114 (accept_3_4 31 35 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 35 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 29
  35 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 114 (accept_3_4 28 35
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 114
  (Polychromatic418967fa.accept_13_1_9_10_1_625 27 35 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 114 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 35 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 114 (accept_3_4 25 35 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 114 (Polychromatic418967fa.accept_21_3_14_9_1_5299 24 35 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 114
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 35 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 114 (accept_3_4 22 35 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 114 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 35 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 114 (accept_3_4 19 35 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 114 (Polychromatic418967fa.accept_15_3_5_9_1_764 18 35 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 114 (accept_3_4 16 35 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 114 (Polychromatic418967fa.accept_16_15_3_2_1_4170 15 35 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 114 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 35 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 114 (accept_3_4 13 35 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 35 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 114
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 35 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 114 (accept_3_4 10 35 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 114 (Polychromatic418967fa.accept_20_8_15_14_1_1487 8 35 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 114 (accept_3_4 7 35 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 114 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 35 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 114 (accept_3_4 4 35 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 35
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 114
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 35 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 114 (accept_3_4 1 35 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  114))))))))))))))))))))))))))))))))))) (allB_succ 34 114 (allA_succ_of_accept 33 34 114
  (Polychromatic418967fa.accept_12_9_10_6_1_872 33 34 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 114 2 16 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 34 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 114 2 15 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 114 (accept_3_5 29 34 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 114 2 14 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 114 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 34 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 114 2 13 17 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 114
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 34 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 114 2 12 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 114 (accept_3_5 23 34 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  114 2 11 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 114 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 34 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 114 2 10 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 34 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 114 2 9 17 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 114 (accept_3_5 17 34 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 114 2 8 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 34 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 114 2 7 17 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 114
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 34 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 114 2 6 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 114 (accept_3_5 11 34 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  114 2 5 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 114 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 34 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 114 2 4 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 114 (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 34 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 114 2 3 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 114 (accept_3_5 5 34 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 114 2 2 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 34 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 114 2 1 17 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 114
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 34 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 114)))))))))))))))))))))))))))))))))) (allB_succ 33 114 (allA_succ_of_accept 32 33 114
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 33 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 33 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 114 3 10 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 114 (Polychromatic418967fa.accept_10_9_3_4_1_985 29
  33 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 114
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 33 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 33 114 3 9 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 33 114 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 33 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 33 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 114 3 8 11 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 114 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 33 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 33 114 3 7 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 114 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 33 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 33 114 3 6 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 33 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 33 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 114 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 33 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 114 3 5 11 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 114
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 33 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 114 (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 33 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 114 3 4 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 33 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 114
  (Polychromatic418967fa.accept_7_3_5_2_1_17 10 33 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 33 114 3 3 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 33 114 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 33 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 114 3 2 11 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 114
  (Polychromatic418967fa.accept_15_5_3_9_1_283 5 33 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 33 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 114 3 1 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 114 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 33 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 114
  (Polychromatic418967fa.accept_17_1_16_12_1_5298 1 33 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 114))))))))))))))))))))))))))))))))) (allB_succ 32 114 (allA_succ_of_accept 31 32 114 (accept_3_4 31 32
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 114 2 15 16 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 114
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 32 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 114 2 14 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 114 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 32 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 114 2 13 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 114 (accept_3_4 25 32 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 114 2 12 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 114 (Polychromatic418967fa.accept_14_9_4_2_1_983 23 32 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 114 2 11 16 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 114
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 114 2 10 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 114 (accept_3_4 19 32 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  114 2 9 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 114 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 32 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 114 2 8 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 114 (Polychromatic418967fa.accept_12_3_8_6_1_895 15 32 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 114 2 7 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 114 (accept_3_4 13 32 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 114 2 6 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 114 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 32 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 114 2 5 16 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 114
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 32 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 114 2 4 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 114 (accept_3_4 7 32 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 114
  2 3 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  114 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 32 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 114 2 2 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 32 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 114 2 1 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 114 (accept_3_4 1 32 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 114)))))))))))))))))))))))))))))))) (allB_succ 31 114 (allA_succ_of_accept 30 31 114
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 114 (accept_3_5 29 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 31 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 114 (accept_3_5 26 31 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 114
  (Polychromatic418967fa.accept_11_2_9_4_1_310 24 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 114 (accept_3_5 23 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 114 (accept_3_5 20 31 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 31 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 114
  (Polychromatic418967fa.accept_21_18_10_9_1_5297 18 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 114 (accept_3_5 17 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 31 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 114 (accept_3_5 14 31 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 114
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 114 (accept_3_5 11 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 114 (accept_3_5 8 31 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 31 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 114
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 114 (accept_3_5 5 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  114 (Polychromatic418967fa.accept_13_4_5_10_1_1247 4 31 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 114 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 31 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 114 (accept_3_5 2 31 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 114))))))))))))))))))))))))))))))) (allB_succ 30 114
  (allA_succ_of_accept 29 30 114 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 30 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 114 2 14 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 30 114 3 9 10 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 30 114 2 13 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 114 (Polychromatic418967fa.accept_9_7_3_6_1_270 25
  30 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 114 6 4 5 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 114
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 30 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 114 2 11 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 30 114 3 7 10 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 30 114 2 10 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 30 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 114 6 3 5 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 114 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 30 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 114 2 8 15 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 114 3 5 10 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 114 2 7 15 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 114
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 30 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 114 6 2 5 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 114 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 30 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 114 2 5 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 114 3 3 10 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 30 114 2 4 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 114 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 30 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 114 6 1 5 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 114
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 30 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 114 2 2 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 30 114 3 1 10 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 30 114 2 1 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 30 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 114)))))))))))))))))))))))))))))) (allB_succ 29 114 (allA_succ_of_accept
  28 29 114 (accept_3_4 28 29 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 114 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 29 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 114 (accept_3_4 25 29 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 29 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  29 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 114 (accept_3_4 22 29
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 114
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 29 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 114 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 29 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 114 (accept_3_4 19 29 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 114 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 29 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 17
  29 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 114 (accept_3_4 16 29
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 114 (Polychromatic418967fa.accept_4_3_1_2_1_62
  15 29 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 114
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 29 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 114 (accept_3_4 13 29 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 114 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 29 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 114 (accept_3_4 10 29 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 114 (Polychromatic418967fa.accept_27_9_2_6_1_5296 9 29 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 114
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 29 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 114 (accept_3_4 7 29 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  114 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 29 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 114 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 29 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 114 (accept_3_4 4 29 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 114 (Polychromatic418967fa.accept_13_2_3_10_1_658 2
  29 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 114 (accept_3_4 1 29 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 114))))))))))))))))))))))))))))) (allB_succ 28 114
  (allA_succ_of_accept 27 28 114 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 28 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 114 2 13 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 25
  28 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 114 2 12 14 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 114 (accept_3_5 23
  28 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 114 2 11 14 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 114
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 28 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 28 114 2 10 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 28 114 (Polychromatic418967fa.accept_10_9_8_4_1_970 19 28 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 114 2 9 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 114 (accept_3_5 17 28 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 28 114 2 8 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 28 114 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 28 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 114 2 7 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 114 (Polychromatic418967fa.accept_9_4_1_6_1_284 13
  28 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 114 2 6 14 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 114 (accept_3_5 11
  28 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 114 2 5 14 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 114
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 28 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 28 114 2 4 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 28 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 28 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 114 2 3 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 114 (accept_3_5 5 28 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 28 114 2 2 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 28 114 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 28 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 114 2 1 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 114 (Polychromatic418967fa.accept_16_1_12_2_1_2136 1
  28 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 114))))))))))))))))))))))))))))
  (allB_succ 27 114 (allA_succ_of_accept 26 27 114 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 27 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 27 114 3 8 9 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 27 114 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 27 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 27 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 114 3 7 9 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 114
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 27 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 114 (Polychromatic418967fa.accept_15_4_12_9_1_773 19 27 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 114 3 6 9 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 114
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 27 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 27 114 3 5 9 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 27 114 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 27 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 114 3 4 9 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 114
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 27 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 27 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 114 3 3 9 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 27 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 114
  (Polychromatic418967fa.accept_16_7_11_2_1_3117 7 27 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 27 114 3 2 9 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 27 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 114 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 27 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 114 3 1 9 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 114
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 27 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 114))))))))))))))))))))))))))) (allB_succ 26 114 (allA_succ_of_accept 25
  26 114 (accept_3_4 25 26 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 114 2 12 13 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 114
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 26 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 26 114 2 11 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 26 114 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 26 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 114 2 10 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 114 (accept_3_4 19 26 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 114 2 9 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 26 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 26 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 114 2 8 13 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 114
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 26 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 114 2 7 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 114 (accept_3_4 13 26 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  114 2 6 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 114 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 26 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 114 2 5 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 114 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 26 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 114 2 4 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 114 (accept_3_4 7 26 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 114 2 3 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 114 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 26 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 114 2 2 13 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 114
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 26 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 114 2 1 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 114 (accept_3_4 1 26 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  114)))))))))))))))))))))))))) (allB_succ 25 114 (allA_succ_of_accept 24 25 114
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 25 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 25 114 (accept_3_5 23 25 114 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 25 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 25 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 114 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 25 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 114 (accept_3_5 20 25 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  25 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 114
  (Polychromatic418967fa.accept_11_7_3_4_1_729 18 25 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 114 (accept_3_5 17 25 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 114 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 25 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 114 (accept_3_5 14 25 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 114 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 25 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 114
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 25 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 114 (accept_3_5 11 25 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 25 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 114 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 25 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 114 (accept_3_5 8 25 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 114
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 25 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 114 (accept_3_5 5 25 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  114 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 25 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 114 (accept_3_5 2 25 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 25 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 114))))))))))))))))))))))))) (allB_succ 24 114
  (allA_succ_of_accept 23 24 114 (Polychromatic418967fa.accept_20_3_4_14_1_3918 23 24 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 114 2 11 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 114 3 7 8 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 114 2 10 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 19
  24 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 114 6 3 4 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 114
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 24 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 24 114 2 8 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 24 114 3 5 8 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 24 114 2 7 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 24 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 114 6 2 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 114 (Polychromatic418967fa.accept_25_11_24_14_1_5295 11 24
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 114 2 5 12 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 114 3 3 8 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 114 2 4 12 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 114
  (Polychromatic418967fa.accept_21_7_3_9_1_5294 7 24 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 114 6 1 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 114 2 2 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 114 3 1 8 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 114 2 1 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 24 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 114)))))))))))))))))))))))) (allB_succ 23
  114 (allA_succ_of_accept 22 23 114 (accept_3_4 22 23 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 23 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 114 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 23 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 114 (accept_3_4 19 23 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 114 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 23 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 114 (accept_3_4 16 23 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 114 (Polychromatic418967fa.accept_18_15_5_6_1_5293 15 23 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 114 (Polychromatic418967fa.accept_15_14_8_9_1_1452 14 23 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 114 (accept_3_4 13 23 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 23 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 114
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 23 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 114 (accept_3_4 10 23 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 114 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 23 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 114 (accept_3_4 7 23 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 114 (Polychromatic418967fa.accept_21_6_2_9_1_5292 6 23 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 114 (accept_3_4 4 23 114
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  23 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 114
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 23 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 114 (accept_3_4 1 23 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  114))))))))))))))))))))))) (allB_succ 22 114 (allA_succ_of_accept 21 22 114
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 22 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 114 2 10 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 22 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 114 2 9 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 114 (accept_3_5 17 22 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 114 2 8 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 114 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 22 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 114 2 7 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 114 (Polychromatic418967fa.accept_7_6_1_2_1_230 13
  22 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 114 2 6 11 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 114 (accept_3_5 11
  22 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 114 2 5 11 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 114
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 22 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 114 2 4 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 114 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 22 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 114 2 3 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 114 (accept_3_5 5 22 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 114 2 2 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 22 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 114 2 1 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 22
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 114)))))))))))))))))))))) (allB_succ 21
  114 (allA_succ_of_accept 20 21 114 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 21 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 114 3 6 7 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 114
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 21 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 114 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 114 3 5 7 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 21 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 114
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 114 3 4 7 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 21 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 114 3 3 7 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 114
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 114 3 2 7 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 114
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 21 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 114 3 1 7 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 114 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 21 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 114 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 21 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 114))))))))))))))))))))) (allB_succ 20 114
  (allA_succ_of_accept 19 20 114 (accept_3_4 19 20 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20
  114 2 9 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  20 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 20 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 20 114 2 8 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 20 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 20 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 114 2 7 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 114 (accept_3_4 13 20 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 114 2 6 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 20 114 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 20 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 114 2 5 10 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 114
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 20 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 114 2 4 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 114 (accept_3_4 7 20 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 114
  2 3 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  114 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 20 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 114 2 2 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 20 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 114 2 1 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 114 (accept_3_4 1 20 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 114)))))))))))))))))))) (allB_succ 19 114 (allA_succ_of_accept 18 19 114
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 19 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 114 (accept_3_5 17 19 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 19 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 114 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 19 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 114 (accept_3_5 14 19 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 114
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 19 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 114 (accept_3_5 11 19 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 19 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 114 (accept_3_5 8 19 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 19 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 114
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 6 19 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 114 (accept_3_5 5 19 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  114 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 19 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 114 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 19 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 114 (accept_3_5 2 19 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 114))))))))))))))))))) (allB_succ 18 114 (allA_succ_of_accept 17
  18 114 (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 18 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 18 114 2 8 9 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 18 114 3 5 6 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 18 114 2 7 9 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 114 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 18 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 114 6 2 3 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 114 (Polychromatic418967fa.accept_21_11_18_9_1_465
  11 18 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 114 2 5 9 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 18 114 3 3 6 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 18 114 2 4 9 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 114
  (Polychromatic418967fa.accept_21_7_18_9_1_5291 7 18 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 114 6 1 3 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 114 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 18 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 114 2 2 9 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 114 3 1 6 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 114 2 1 9 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 114 (Polychromatic418967fa.accept_21_1_18_9_1_5290 1 18 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 114)))))))))))))))))) (allB_succ 17 114
  (allA_succ_of_accept 16 17 114 (accept_3_4 16 17 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 114 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 17 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 114 (accept_3_4 13 17 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 114 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 17 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 114 (accept_3_4 10 17 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 114 (Polychromatic418967fa.accept_16_9_1_2_1_2126 9 17 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 114 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 17 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 114 (accept_3_4 7 17 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 114 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 17 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 114
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 17 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 114 (accept_3_4 4 17 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 114 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 17 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 114 (accept_3_4 1 17 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 114))))))))))))))))) (allB_succ 16 114 (allA_succ_of_accept 15 16 114
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 16 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 114 2 7 8 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 114 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 16 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 114 2 6 8 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 114 (accept_3_5 11 16 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 114 2 5 8 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 114 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 16 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 114 2 4 8 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 114 (Polychromatic418967fa.accept_13_7_3_10_1_656 7
  16 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 114 2 3 8 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 114 (accept_3_5 5 16
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 114 2 2 8 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 114
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 16 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 114 2 1 8 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 114 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 16 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 114)))))))))))))))) (allB_succ 15 114 (allA_succ_of_accept 14 15 114
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 15 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 114 3 4 5 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 114 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 15 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 114
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 15 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 114 3 3 5 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 114 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 15 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 114 (Polychromatic418967fa.accept_21_7_15_9_1_5289 7 15 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 114 3 2 5 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 114 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 15 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 114 3 1 5 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 114 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 15 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 114
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 114))))))))))))))) (allB_succ 14 114 (allA_succ_of_accept 13 14 114 (accept_3_4 13 14 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 114 2 6 7 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 114 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 14 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 114 2 5 7 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 114
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 14 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 114 2 4 7 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 14 114 (accept_3_4 7 14 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 114
  2 3 7 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 114
  (Polychromatic418967fa.accept_15_5_14_9_1_274 5 14 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 114 2 2 7 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 114 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 14 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 114 2 1 7 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 114 (accept_3_4 1 14 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 114)))))))))))))) (allB_succ 13 114 (allA_succ_of_accept 12 13 114
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 13 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 114 (accept_3_5 11 13 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 114 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 13 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 114 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 13 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 114 (accept_3_5 8 13 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 114
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 13 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 114 (accept_3_5 5 13 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  114 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 13 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 114 (accept_3_5 2 13 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 13 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 114))))))))))))) (allB_succ 12 114 (allA_succ_of_accept 11 12
  114 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 114 2 5 6 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 12 114 3 3 4 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 12 114 2 4 6 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 114 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 12 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 114 6 1 2 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 114 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 12 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 114 2 2 6 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 12 114 3 1 4 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 12 114 2 1 6 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 114
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 12 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 114)))))))))))) (allB_succ 11 114 (allA_succ_of_accept 10 11 114 (accept_3_4 10 11 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 114
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 11 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 114 (accept_3_4 7 11 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  114 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 11 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 114 (accept_3_4 4 11 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 114 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 11 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 114 (Polychromatic418967fa.accept_13_2_11_10_1_1881
  2 11 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 114 (accept_3_4 1 11
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 114))))))))))) (allB_succ 10 114 (allA_succ_of_accept 9 10
  114 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 10 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 10 114 2 4 5 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 10 114 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 10 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 114 2 3 5 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 114 (accept_3_5 5 10 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 114 2 2 5 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 10 114 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 10 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 114 2 1 5 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 114
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 10 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 114)))))))))) (allB_succ 9 114 (allA_succ_of_accept 8 9 114 (Polychromatic418967fa.accept_10_8_9_4_1_961
  8 9 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 114
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 9 114 3 2 3 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 9 114 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 9 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 114 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 9 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 114 3 1 3 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 114
  (Polychromatic418967fa.accept_11_2_9_4_1_310 2 9 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 114 (Polychromatic418967fa.accept_13_1_9_10_1_625 1 9 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 9 114))))))))) (allB_succ 8 114 (allA_succ_of_accept 7 8 114 (accept_3_4 7 8
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 114 2 3 4 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 114
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 8 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 114 2 2 4 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 114 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 8 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 114 2 1 4 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 114 (accept_3_4 1 8 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 114)))))))) (allB_succ 7 114 (allA_succ_of_accept 6 7 114
  (Polychromatic418967fa.accept_21_6_7_9_1_5288 6 7 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 114 (accept_3_5 5 7 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 114
  (Polychromatic418967fa.accept_9_4_7_6_1_255 4 7 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 114 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 7 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 114 (accept_3_5 2 7 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 114))))))) (allB_succ 6 114 (allA_succ_of_accept 5 6 114
  (Polychromatic418967fa.accept_10_5_6_4_1_64 5 6 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 114 2 2 3 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 6 114 3 1 2 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 6 114 2 1 3 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 114 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 6 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 114)))))) (allB_succ 5 114 (allA_succ_of_accept 4 5 114 (accept_3_4 4 5
  114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 114 (Polychromatic418967fa.accept_4_3_1_2_1_62 3
  5 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 114
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 5 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 114 (accept_3_4 1 5 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 114)))))
  (allB_succ 4 114 (allA_succ_of_accept 3 4 114 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 4 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 114 2 1 2 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 114 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 4 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 114)))) (allB_succ 3 114 (allA_succ_of_accept
  2 3 114 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 3 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 114 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 114))) (allB_succ 2 114 (allA_succ_of_accept 1 2 114 (accept_3_4
  1 2 114 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 114)) (allB_two
  114))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


