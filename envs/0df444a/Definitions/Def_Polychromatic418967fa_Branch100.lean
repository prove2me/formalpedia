-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch100
-- name    : Polychromatic418967fa_Branch100
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:10:01.787814+00:00
-- url     : https://prove2.me/theorems/76bf67fd-cbbe-4cac-94d9-38a326074ece
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

def Polychromatic418967fa.branch_100 : allB 100 100 :=
  allB_succ' 2 99 100 (Eq.refl Bool.true) (allA_succ_of_accept 1 99 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 99
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 100)) (allB_succ' 3 98 100 (Eq.refl
  Bool.true) (allA_of_3_1 3 98 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 97 100 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 97 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 97 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 100 (accept_3_3 2 97 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 97 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 100)))) (allB_succ' 5 96 100 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 96 100 4 1 24 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 96 100 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 96 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 100 2 1 48 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 100 (Polychromatic418967fa.accept_13_1_5_9_1_226 1 96 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 100))))) (allB_succ' 6 95 100 (Eq.refl
  Bool.true) (allA_of_3_1 6 95 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 94 100 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 94 100 2 3 47 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 94 100 (accept_3_3 5 94 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 100
  2 2 47 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 94
  100 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 94 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 94 100 2 1 47 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 94 100 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 94 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 94 100))))))) (allB_succ' 8 93 100 (Eq.refl Bool.true) (allA_succ_of_accept
  7 93 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 93 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 93 100 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 93 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 100 (accept_3_3 5 93 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 100 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 93 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 100
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 93 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 93 100 (accept_3_3 2 93 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93
  100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 93 100)))))))) (allB_succ' 9 92 100 (Eq.refl Bool.true) (allA_of_3_1 9 92 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 10 91 100 (Eq.refl Bool.true) (allA_succ_of_accept 9 91 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 91 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 100 (accept_3_3 8 91 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  100 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 91 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 100 (Polychromatic418967fa.accept_15_6_1_10_1_1549 6 91 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 100 (accept_3_3 5 91 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 100 (Polychromatic418967fa.accept_19_4_15_5_1_3043 4 91 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 100 (accept_3_3 2 91 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 100 (Polychromatic418967fa.accept_19_1_15_5_1_4357
  1 91 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 100)))))))))) (allB_succ' 11 90 100
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 90 100 10 1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 90 100 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 90 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 100 2 4 45 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 100
  (Polychromatic418967fa.accept_17_7_5_15_1_3184 7 90 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 90 100 2 3 45 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 90 100 5 1 18 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 90 100 2 2 45 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 90 100 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 90 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 100 2 1 45 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 90 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90 100))))))))))) (allB_succ' 12 89 100
  (Eq.refl Bool.true) (allA_of_3_1 12 89 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 88 100 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 88 100 4 3 22 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 88 100 (accept_3_3 11 88 100 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 88 100 2 5 44 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 88 100 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 88 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 100 4 2 22 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 100 (Polychromatic418967fa.accept_16_7_8_4_1_689 7 88 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 100 2 3 44 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 100 (accept_3_3 5 88 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 100 4 1 22 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88 100 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 88
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 100 2 1 44 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 100
  (Polychromatic418967fa.accept_13_1_10_9_1_215 1 88 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 100))))))))))))) (allB_succ' 14 87 100 (Eq.refl Bool.true) (allA_succ_of_accept 13 87 100
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 87 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 87 100 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 87 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 100 (accept_3_3 11 87 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 87 100 (Polychromatic418967fa.accept_17_10_2_15_1_3179 10 87 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 100
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 87 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 100 (accept_3_3 8 87 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 100 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 87 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 100 (accept_3_3 5 87 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 100 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 87 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 100 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 100 (accept_3_3 2 87 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 87
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 100)))))))))))))) (allB_succ' 15 86 100
  (Eq.refl Bool.true) (allA_of_3_1 15 86 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 85 100 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 85 100 5 3 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 85 100 (accept_3_3 14 85 100 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 85 100 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 85 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 100 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 85 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 100 (accept_3_3 11 85 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 85 100 5 2 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 85 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 100 (accept_3_3 8 85 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 100 (Polychromatic418967fa.accept_9_7_4_1_1_391 7
  85 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 100
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 85 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 85 100 5 1 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 85 100 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 85 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 85 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 100 (accept_3_3 2 85 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 100 (Polychromatic418967fa.accept_8_1_5_4_1_388 1
  85 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 100)))))))))))))))) (allB_succ' 17 84
  100 (Eq.refl Bool.true) (allA_succ_of_gcd 16 84 100 4 4 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 84 100 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 84 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 100 2 7 42 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 100
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 84 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 100 4 3 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 100 (accept_3_3 11 84 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84
  100 2 5 42 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  84 100 (Polychromatic418967fa.accept_18_9_12_10_1_387 9 84 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 84 100 4 2 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 84 100 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 84 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 100 2 3 42 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 100 (accept_3_3 5 84 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 100 4 1 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 84 100 (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 84 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 100 2 1 42 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 100
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 1 84 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 100))))))))))))))))) (allB_succ' 18 83 100 (Eq.refl Bool.true) (allA_of_3_1 18 83 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 19 82 100 (Eq.refl Bool.true) (allA_succ_of_gcd 18 82 100 2 9 41 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 100 (accept_3_3 17
  82 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82 100 2 8 41 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 82 100
  (Polychromatic418967fa.accept_19_15_6_5_1_4356 15 82 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 82 100 2 7 41 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 82 100 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 82 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 100 2 6 41 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 100 (accept_3_3 11 82 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 82 100 2 5 41 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 82 100 (Polychromatic418967fa.accept_27_9_1_19_1_4355 9 82 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 82 100 2 4 41 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 82 100 (Polychromatic418967fa.accept_12_7_10_4_1_382 7
  82 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 100 2 3 41 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 100 (accept_3_3 5 82
  100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 100 2 2 41 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 82 100
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 82 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 82 100 2 1 41 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 82 100 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 82 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 82 100))))))))))))))))))) (allB_succ' 20 81 100 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 81 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 81 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 100 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 81 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 100 (accept_3_3 17 81 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 100 (Polychromatic418967fa.accept_15_1_6_10_1_23
  16 81 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 100
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 15 81 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 100 (accept_3_3 14 81 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 100 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 81 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 100 (accept_3_3 11 81 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 100 (Polychromatic418967fa.accept_22_10_15_12_1_4354 10 81 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 100
  (Polychromatic418967fa.accept_14_9_11_2_1_2501 9 81 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 100 (accept_3_3 8 81 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 81 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 100 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 81 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 100 (accept_3_3 5 81 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 100 (Polychromatic418967fa.accept_15_4_6_10_1_823 4 81 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 100 (Polychromatic418967fa.accept_15_3_6_10_1_1539
  3 81 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 100 (accept_3_3 2 81
  100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  81 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 100)))))))))))))))))))) (allB_succ'
  21 80 100 (Eq.refl Bool.true) (allA_of_3_1 21 80 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 79 100
  (Eq.refl Bool.true) (allA_succ_of_accept 21 79 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 79 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 100 (accept_3_3 20 79 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 100 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 79 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 100
  (Polychromatic418967fa.accept_13_5_1_9_1_618 18 79 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 100 (accept_3_3 17 79 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 100 (Polychromatic418967fa.accept_17_16_11_15_1_4353 16 79 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 100 (accept_3_3 14 79 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 100 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 79 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 100
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 79 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 100 (accept_3_3 11 79 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 100 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 79 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 79 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 100 (accept_3_3 8 79 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 100 (Polychromatic418967fa.accept_14_7_9_2_1_2489 7 79 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 100
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 79 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 100 (accept_3_3 5 79 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  100 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 79 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 100 (accept_3_3 2 79 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 100 (Polychromatic418967fa.accept_19_1_3_5_1_3092 1 79 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 100)))))))))))))))))))))) (allB_succ' 23 78 100 (Eq.refl
  Bool.true) (allA_succ_of_gcd 22 78 100 2 11 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 78 100 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 78 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 100 2 10 39 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 100
  (Polychromatic418967fa.accept_17_2_10_15_1_1238 19 78 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 100 2 9 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 100 (accept_3_3 17 78 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78
  100 2 8 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  78 100 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 78 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 78 100 2 7 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 78 100 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 78 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 100 2 6 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 100 (accept_3_3 11 78 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 100 2 5 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 78 100 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 78 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 100 2 4 39 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 100
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 78 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 100 2 3 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 100 (accept_3_3 5 78 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 100
  2 2 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78
  100 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 78 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 100 2 1 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 100 (Polychromatic418967fa.accept_14_1_8_2_1_1675 1 78 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78 100))))))))))))))))))))))) (allB_succ' 24 77 100 (Eq.refl Bool.true)
  (allA_of_3_1 24 77 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 76 100 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 76 100 4 6 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 76 100 (accept_3_3 23 76 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76
  100 2 11 38 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  76 100 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 76 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 76 100 4 5 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 76 100 (Polychromatic418967fa.accept_16_3_12_4_1_170 19 76 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 100 2 9 38 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 100 (accept_3_3 17 76 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76 100 4 4 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 76 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 76 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 100 2 7 38 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 100
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 76 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 76 100 4 3 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 76 100 (accept_3_3 11 76 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76
  100 2 5 38 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  76 100 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 76 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 76 100 4 2 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 76 100 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 76 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 100 2 3 38 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 100 (accept_3_3 5 76 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 100 4 1 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 76 100 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 76 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 100 2 1 38 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 100
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 76 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 100))))))))))))))))))))))))) (allB_succ' 26 75 100 (Eq.refl Bool.true) (allA_succ_of_gcd 25 75 100 25 1 3
  4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 75 100
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 75 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 100 (accept_3_3 23 75 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 100 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 75 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 100 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 75 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 75 100 5 4 15 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 100
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 75 100 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 75 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 100 (accept_3_3 17 75 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 75 100 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 75 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 100 5 3 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 100 (accept_3_3 14 75 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 75 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 100
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 75 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 100 (accept_3_3 11 75 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75
  100 5 2 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  75 100 (Polychromatic418967fa.accept_16_9_11_4_1_3194 9 75 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 75 100 (accept_3_3 8 75 100 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 100 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 75 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 75 100 5 1 15 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 100
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 75 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 100 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 100 (accept_3_3 2 75 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 75 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 100)))))))))))))))))))))))))) (allB_succ' 27 74 100 (Eq.refl
  Bool.true) (allA_of_3_1 27 74 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 73 100 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 73 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 73 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 100 (accept_3_3 26 73 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 73 100 (Polychromatic418967fa.accept_13_12_8_9_1_1833 25 73 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 100
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 73 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 100 (accept_3_3 23 73 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 100 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 73 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 100 (accept_3_3 20 73 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 100 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 73 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 100
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 73 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 100 (accept_3_3 17 73 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 100 (Polychromatic418967fa.accept_13_3_8_9_1_1134 16 73 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 73 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 100 (accept_3_3 14 73 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 100 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 73 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 100
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 73 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 100 (accept_3_3 11 73 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 100 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 73 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 100 (accept_3_3 8 73 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 100 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 73 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 100
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 73 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 100 (accept_3_3 5 73 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  100 (Polychromatic418967fa.accept_13_4_8_9_1_1156 4 73 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 73 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 100 (accept_3_3 2 73 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 100 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 73 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 100)))))))))))))))))))))))))))) (allB_succ' 29 72 100
  (Eq.refl Bool.true) (allA_succ_of_gcd 28 72 100 4 7 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 72 100 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 72 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 100 2 13 36 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 100
  (Polychromatic418967fa.accept_16_9_8_4_1_1354 25 72 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 100 4 6 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 100 (accept_3_3 23 72 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72
  100 2 11 36 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  72 100 (Polychromatic418967fa.accept_13_8_7_9_1_611 21 72 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 72 100 4 5 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 72 100 (Polychromatic418967fa.accept_13_6_7_9_1_1848 19 72 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 100 2 9 36 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 100 (accept_3_3 17 72 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 100 4 4 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 72 100 (Polychromatic418967fa.accept_13_2_7_9_1_2616 15 72 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 100 2 7 36 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 100
  (Polychromatic418967fa.accept_15_13_12_10_1_4352 13 72 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 72 100 4 3 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 72 100 (accept_3_3 11 72 100 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 72 100 2 5 36 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 72 100 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 72 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 100 4 2 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 100 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 72 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 100 2 3 36 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 100 (accept_3_3 5 72 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 100 4 1 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72 100 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3
  72 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 100 2 1 36 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 100
  (Polychromatic418967fa.accept_16_1_8_4_1_4334 1 72 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 100))))))))))))))))))))))))))))) (allB_succ' 30 71 100 (Eq.refl Bool.true) (allA_of_3_1 30 71 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 70 100 (Eq.refl Bool.true) (allA_succ_of_gcd 30 70 100 10 3 7
  10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 100
  (accept_3_3 29 70 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 100 2 14 35 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 100
  (Polychromatic418967fa.accept_13_1_5_9_1_226 27 70 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 70 100 2 13 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 25 70 100 5 5 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 70 100 2 12 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 70 100 (accept_3_3 23 70 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70
  100 2 11 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  70 100 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 70 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 70 100 10 2 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 70 100 (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 70 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 100 2 9 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 100 (accept_3_3 17 70 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70 100 2 8 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 70 100 5 3 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 70 100 2 7 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 70 100 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 70 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 100 2 6 35 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 100 (accept_3_3 11 70 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 100 10 1 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 100 (Polychromatic418967fa.accept_19_9_13_5_1_4351 9 70 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 100 2 4 35 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 70 100
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 70 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 70 100 2 3 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 70 100 5 1 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 70 100 2 2 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 70 100 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 70 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 100 2 1 35 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 100 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 70 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70 100)))))))))))))))))))))))))))))))
  (allB_succ' 32 69 100 (Eq.refl Bool.true) (allA_succ_of_accept 31 69 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  69 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 100
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 69 100 (accept_3_3 29 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  69 100 (Polychromatic418967fa.accept_16_12_5_4_1_3275 28 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 69 100 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 69 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 100 (accept_3_3 26 69 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 100
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 69 100 (accept_3_3 23 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  69 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 69 100 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 69 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 100 (accept_3_3 20 69 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 69 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 100
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 100 (accept_3_3 17 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  69 100 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 69 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 69 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 100 (accept_3_3 14 69 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 100
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 69 100 (accept_3_3 11 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  69 100 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 69 100 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 69 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 100 (accept_3_3 8 69 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 69 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 100
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 100 (accept_3_3 5 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69
  100 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 69 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 69 100 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 69 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 100 (accept_3_3 2 69 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 69 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69 100)))))))))))))))))))))))))))))))) (allB_succ' 33 68 100
  (Eq.refl Bool.true) (allA_of_3_1 33 68 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 67 100 (Eq.refl
  Bool.true) (allA_succ_of_accept 33 67 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 67 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 100 (accept_3_3 32 67 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 100 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 67 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 100
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 100 (accept_3_3 29 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 100 (Polychromatic418967fa.accept_16_12_3_4_1_4317 28 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 100 (accept_3_3 26 67 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 100 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 67 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 100
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 100 (accept_3_3 23 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 100 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 67 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 100 (accept_3_3 20 67 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 100 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 67 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 100
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 100 (accept_3_3 17 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 100 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 100 (accept_3_3 14 67 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 100 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 67 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 100
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 100 (accept_3_3 11 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 100 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 67 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 100 (accept_3_3 8 67 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 100 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 67 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 100
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 100 (accept_3_3 5 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  100 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 67 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 100 (accept_3_3 2 67 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 100 (Polychromatic418967fa.accept_13_1_2_9_1_1186 1 67 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 100)))))))))))))))))))))))))))))))))) (allB_succ' 35
  66 100 (Eq.refl Bool.true) (allA_succ_of_gcd 34 66 100 2 17 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 100 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 66 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 100 2 16 33 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 100
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 66 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 100 2 15 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 100 (accept_3_3 29 66 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66
  100 2 14 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  66 100 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 66 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 66 100 2 13 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 66 100 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 66 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 100 2 12 33 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 100 (accept_3_3 23 66 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 100 2 11 33 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 100
  (Polychromatic418967fa.accept_12_9_6_4_1_402 21 66 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 100 2 10 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 100 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 66 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 100 2 9 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 100 (accept_3_3 17 66 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 66 100 2 8 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 66 100 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 66 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 100 2 7 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 100 (Polychromatic418967fa.accept_7_6_3_2_1_461 13
  66 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 100 2 6 33 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 100 (accept_3_3 11
  66 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 100 2 5 33 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 100
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 66 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 100 2 4 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 100 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 66 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 100 2 3 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 100 (accept_3_3 5 66 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 66 100 2 2 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 66 100 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 66 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 100 2 1 33 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 100 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 66
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66 100)))))))))))))))))))))))))))))))))))
  (allB_succ' 36 65 100 (Eq.refl Bool.true) (allA_of_3_1 36 65 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  37 64 100 (Eq.refl Bool.true) (allA_succ_of_gcd 36 64 100 4 9 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 100 (accept_3_3 35 64 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 64 100 2 17 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 64 100 (Polychromatic418967fa.accept_23_10_18_8_1_4350 33 64 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 100 4 8 16 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 100
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 64 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 100 2 15 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 64 100 (accept_3_3 29 64 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64
  100 4 7 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  64 100 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 64 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 64 100 2 13 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 64 100 (Polychromatic418967fa.accept_17_8_13_15_1_2143 25 64 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 100 4 6 16 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 100 (accept_3_3 23 64 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 100 2 11 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 100 (Polychromatic418967fa.accept_11_10_9_1_1_2186
  21 64 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 100 4 5 16 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 100
  (Polychromatic418967fa.accept_17_2_13_15_1_4349 19 64 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 100 2 9 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 100 (accept_3_3 17 64 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  100 4 4 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 100 (Polychromatic418967fa.accept_14_1_8_2_1_1675 15 64 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 100 2 7 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 64 100 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 64 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 100 4 3 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 100 (accept_3_3 11 64 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 100 2 5 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 64 100 (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 64 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 100 4 2 16 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 100
  (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 64 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 64 100 2 3 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 64 100 (accept_3_3 5 64 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 100
  4 1 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64
  100 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 64 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 64 100 2 1 32 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 64 100 (Polychromatic418967fa.accept_14_1_8_2_1_1675 1 64 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 64 100))))))))))))))))))))))))))))))))))))) (allB_succ' 38 63 100 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 63 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 63 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 100 (Polychromatic418967fa.accept_15_6_3_10_1_2341
  36 63 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 100 (accept_3_3 35
  63 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 100
  (Polychromatic418967fa.accept_13_8_11_9_1_593 34 63 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 63 100 (Polychromatic418967fa.accept_13_7_11_9_1_1858 33 63 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 100 (accept_3_3 32 63 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 63 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 100 (Polychromatic418967fa.accept_12_6_3_4_1_394
  30 63 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 100 (accept_3_3 29
  63 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 100
  (Polychromatic418967fa.accept_13_2_11_9_1_591 28 63 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 63 100 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 63 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 100 (accept_3_3 26 63 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 63 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 63 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 100 (Polychromatic418967fa.accept_15_9_3_10_1_2312
  24 63 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 100 (accept_3_3 23
  63 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 100
  (Polychromatic418967fa.accept_15_7_3_10_1_817 22 63 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 63 100 (Polychromatic418967fa.accept_13_8_11_9_1_593 21 63 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 100 (accept_3_3 20 63 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 63 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 100 (Polychromatic418967fa.accept_12_6_3_4_1_394
  18 63 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 100 (accept_3_3 17
  63 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 100
  (Polychromatic418967fa.accept_22_16_19_12_1_4348 16 63 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 63 100 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 63 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 100 (accept_3_3 14 63 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 63 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 100
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 63 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 63 100 (accept_3_3 11 63 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  63 100 (Polychromatic418967fa.accept_27_10_9_19_1_4347 10 63 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 63 100 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 63 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 100 (accept_3_3 8 63 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 100
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 63 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 100 (accept_3_3 5 63 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  100 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 63 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 100 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 100 (accept_3_3 2 63 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 63 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 100)))))))))))))))))))))))))))))))))))))) (allB_succ'
  39 62 100 (Eq.refl Bool.true) (allA_of_3_1 39 62 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 61 100
  (Eq.refl Bool.true) (allA_succ_of_accept 39 61 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 61 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 100 (accept_3_3 38 61 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 100 (Polychromatic418967fa.accept_15_7_1_10_1_305 37 61 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 100
  (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 100 (accept_3_3 35 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 100 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 100 (accept_3_3 32 61 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 100 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 61 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 100
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 100 (accept_3_3 29 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 100 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 61 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 100 (accept_3_3 26 61 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 100 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 61 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 100
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 100 (accept_3_3 23 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 100 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 100 (accept_3_3 20 61 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 100 (Polychromatic418967fa.accept_17_2_10_15_1_1238 19 61 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 100
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 100 (accept_3_3 17 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 100 (Polychromatic418967fa.accept_11_5_6_1_1_988 16 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 61 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 100 (accept_3_3 14 61 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 100 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 61 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 100
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 100 (accept_3_3 11 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 100 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 100 (accept_3_3 8 61 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 100 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 61 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 100
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 100 (accept_3_3 5 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  100 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 61 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 61 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 100 (accept_3_3 2 61 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 100 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 61 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 100)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 60
  100 (Eq.refl Bool.true) (allA_succ_of_gcd 40 60 100 20 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 100 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 60 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 100 2 19 30 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 100
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 37 60 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 100 4 9 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 60 100 5 7 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 60 100 2 17 30 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 60 100 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 60 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 100 4 8 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 100 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 60 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 100 10 3 6 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 100 (accept_3_3 29 60 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 100 4 7 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 100 (Polychromatic418967fa.accept_7_6_4_2_1_236 27
  60 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 100 2 13 30 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 60 100 5 5 12 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 100 4 6 15 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 100 (accept_3_3 23
  60 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 100 2 11 30 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 100
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 60 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 100 20 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 100 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 60 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 100 2 9 30 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 100 (accept_3_3 17 60 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 100 4 4 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 60 100 5 3 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 60 100 2 7 30 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 60 100 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 60 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 100 4 3 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 100 (accept_3_3 11 60 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 100 10 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 60 100 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 60 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 100 4 2 15 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 100
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 60 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 100 2 3 30 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 60 100 5 1 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 60 100 4 1 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 60 100 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 60 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 100 2 1 30 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 100 (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 60 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 100)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 59 100 (Eq.refl Bool.true) (allA_of_3_1 42 59 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  43 58 100 (Eq.refl Bool.true) (allA_succ_of_gcd 42 58 100 2 21 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 100 (accept_3_3 41 58 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 58 100 2 20 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 58 100 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 58 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 58 100 2 19 29 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 58 100
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 58 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 58 100 2 18 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 58 100 (accept_3_3 35 58 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58
  100 2 17 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  58 100 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 58 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 58 100 2 16 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 58 100 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 58 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 58 100 2 15 29 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 58 100 (accept_3_3 29 58 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58 100 2 14 29 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 58 100
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 58 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 58 100 2 13 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 58 100 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 58 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 100 2 12 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 100 (accept_3_3 23 58 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 100 2 11 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 100 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 58 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 100 2 10 29 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 100
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 58 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 100 2 9 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 100 (accept_3_3 17 58 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58
  100 2 8 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  58 100 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 58 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 58 100 2 7 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 58 100 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 58 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 100 2 6 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 100 (accept_3_3 11 58 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 100 2 5 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 58 100 (Polychromatic418967fa.accept_17_9_7_15_1_4346 9 58 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 58 100 2 4 29 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 58 100
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 58 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 58 100 2 3 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 58 100 (accept_3_3 5 58 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 100
  2 2 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 58
  100 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 58 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 58 100 2 1 29 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 58 100 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 58 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 58 100))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 57 100
  (Eq.refl Bool.true) (allA_succ_of_accept 43 57 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 57 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 100
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 100 (accept_3_3 41 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 100 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 100 (Polychromatic418967fa.accept_15_9_12_10_1_809 39 57 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 100 (accept_3_3 38 57 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 100
  (Polychromatic418967fa.accept_11_3_2_1_1_994 36 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 100 (accept_3_3 35 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 100 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 100 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 57 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 100 (accept_3_3 32 57 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 57 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 100
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 100 (accept_3_3 29 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 100 (Polychromatic418967fa.accept_13_2_5_9_1_610 28 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 100 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 57 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 100 (accept_3_3 26 57 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 100
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 100 (accept_3_3 23 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 100 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 100 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 100 (accept_3_3 20 57 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 57 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 100
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 100 (accept_3_3 17 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 100 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 100 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 57 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 100 (accept_3_3 14 57 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 100
  (Polychromatic418967fa.accept_16_12_9_4_1_4345 12 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 100 (accept_3_3 11 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 100 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 100 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 57 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 100 (accept_3_3 8 57 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 57 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 100
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 100 (accept_3_3 5 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  100 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 57 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 100 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 57 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 100 (accept_3_3 2 57 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 100)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45
  56 100 (Eq.refl Bool.true) (allA_of_3_1 45 56 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 55 100
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 55 100 5 9 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 55 100 (accept_3_3 44 55 100 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 55 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 55 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 100 (Polychromatic418967fa.accept_27_15_1_19_1_4344 42 55
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 100 (accept_3_3 41 55 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55 100 5 8 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 55 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 39
  55 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 100 (accept_3_3 38 55
  100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 100
  (Polychromatic418967fa.accept_19_18_17_5_1_4343 37 55 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 55 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 55 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 100 5 7 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 100 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 55 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 55 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 100 (accept_3_3 32 55 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 100 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 55 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 55 100 5 6 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 55 100 (accept_3_3 29 55 100 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 55 100 (Polychromatic418967fa.accept_13_2_3_9_1_2610 28 55 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 100 (accept_3_3 26 55 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55 100 5 5 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 55 100 (Polychromatic418967fa.accept_7_3_6_2_1_90 24
  55 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 100 (accept_3_3 23 55
  100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 100 (Polychromatic418967fa.accept_7_1_6_2_1_18
  22 55 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 55 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 55 100 5 4 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 55 100 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 55 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 100 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 55 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 100 (accept_3_3 17 55 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 100
  (Polychromatic418967fa.accept_17_16_4_15_1_4342 16 55 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 55 100 5 3 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 55 100 (accept_3_3 14 55 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 100 (Polychromatic418967fa.accept_16_13_7_4_1_3248 13 55 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 100 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 55 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 100 (accept_3_3 11 55 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55 100 5 2 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 55 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 55 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 100 (accept_3_3 8 55 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 100 (Polychromatic418967fa.accept_13_7_3_9_1_1142 7
  55 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 100
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 55 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 55 100 5 1 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 55 100 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 55 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 100 (accept_3_3 2 55 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 55
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  100)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 54 100 (Eq.refl Bool.true) (allA_succ_of_gcd 46 54
  100 2 23 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  54 100 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 54 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 54 100 2 22 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 54 100 (Polychromatic418967fa.accept_16_11_6_4_1_2228 43 54 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 100 2 21 27 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 100 (accept_3_3 41 54 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 100 2 20 27 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 100
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 54 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 54 100 2 19 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 54 100 (Polychromatic418967fa.accept_13_11_2_9_1_2640 37 54 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 100 2 18 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 100 (accept_3_3 35 54 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 100 2 17 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 100 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 54 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 100 2 16 27 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 100
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 54 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 100 2 15 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 100 (accept_3_3 29 54 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54
  100 2 14 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  54 100 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 54 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 54 100 2 13 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 54 100 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 54 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 100 2 12 27 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 100 (accept_3_3 23 54 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 100 2 11 27 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 100
  (Polychromatic418967fa.accept_12_9_6_4_1_402 21 54 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 100 2 10 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 54 100 (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 54 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 100 2 9 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 100 (accept_3_3 17 54 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 54 100 2 8 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 54 100 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 54 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 100 2 7 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 100 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  13 54 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 100 2 6 27 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 100 (accept_3_3 11
  54 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 100 2 5 27 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 54 100
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 54 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 54 100 2 4 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 100 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 54 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 100 2 3 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 100 (accept_3_3 5 54 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 54 100 2 2 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 54 100 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 54 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 100 2 1 27 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 100 (Polychromatic418967fa.accept_13_1_2_9_1_1186 1
  54 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  100))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 53 100 (Eq.refl Bool.true) (allA_of_3_1 48 53 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 52 100 (Eq.refl Bool.true) (allA_succ_of_gcd 48 52 100 4 12 13
  25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 100
  (accept_3_3 47 52 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 100 2 23 26 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 100
  (Polychromatic418967fa.accept_21_3_10_16_1_4340 45 52 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 52 100 4 11 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 52 100 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 52 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 100 2 21 26 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 100 (accept_3_3 41 52 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 100 4 10 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 100 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 52 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 52 100 2 19 26 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 52 100
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 37 52 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 52 100 4 9 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 52 100 (accept_3_3 35 52 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52
  100 2 17 26 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  52 100 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 52 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 52 100 4 8 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 52 100 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 52 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 100 2 15 26 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 100 (accept_3_3 29 52 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 100 4 7 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 100 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 52 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 100 2 13 26 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 100
  (Polychromatic418967fa.accept_19_6_14_5_1_4339 25 52 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 100 4 6 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 52 100 (accept_3_3 23 52 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52
  100 2 11 26 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  52 100 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 52 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 52 100 4 5 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 52 100 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 52 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 100 2 9 26 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 100 (accept_3_3 17 52 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 100 4 4 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 52 100 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 52 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 100 2 7 26 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 100
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 52 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 52 100 4 3 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 100 (accept_3_3 11 52 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52
  100 2 5 26 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  52 100 (Polychromatic418967fa.accept_17_9_1_15_1_3156 9 52 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 52 100 4 2 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 52 100 (Polychromatic418967fa.accept_21_7_10_16_1_4338 7 52 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 100 2 3 26 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 100 (accept_3_3 5 52 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 100 4 1 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 52 100 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 52 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 100 2 1 26 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 100
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 52 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 100))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 51 100 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 51 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 51 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 100 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 51 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 100 (accept_3_3 47 51 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 100 (Polychromatic418967fa.accept_14_4_9_2_1_95 46
  51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 100
  (Polychromatic418967fa.accept_18_9_15_10_1_395 45 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 100 (accept_3_3 44 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 100 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 51 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 100 (accept_3_3 41 51 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 100 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 51 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 100
  (Polychromatic418967fa.accept_8_7_3_4_1_404 39 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 100 (accept_3_3 38 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 100 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 51 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 100 (accept_3_3 35 51 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 100 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 51 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 100
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 100 (accept_3_3 32 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 100 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 51 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 100 (accept_3_3 29 51 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 100 (Polychromatic418967fa.accept_11_6_7_1_1_564 28 51 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 100
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 100 (accept_3_3 26 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 100 (Polychromatic418967fa.accept_16_8_3_4_1_3233 24 51 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 100 (accept_3_3 23 51 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 100 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 51 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 100
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 100 (accept_3_3 20 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 100 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 51 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 100 (accept_3_3 17 51 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 100 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 51 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 100
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 100 (accept_3_3 14 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 100 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 51 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 100 (accept_3_3 11 51 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 100 (Polychromatic418967fa.accept_13_10_12_9_1_1837 10 51 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 100
  (Polychromatic418967fa.accept_18_9_15_10_1_395 9 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 100 (accept_3_3 8 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 100 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 51 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 100 (accept_3_3 5 51 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 100 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 51 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 100 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 51
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 100 (accept_3_3 2 51 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 51
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  100)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 100 (allA_of_3_1 50 50 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 100 (allA_succ_of_accept 48 49 100 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 49
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 100 (accept_3_3 47 49 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 100 (Polychromatic418967fa.accept_12_10_1_4_1_392
  46 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 100 (accept_3_3 44 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 100 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 100 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 49 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 100 (accept_3_3 41 49 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 100 (Polychromatic418967fa.accept_13_1_10_9_1_215 40 49 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 100 (accept_3_3 38 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 100 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 100 (Polychromatic418967fa.accept_15_6_4_10_1_2319 36 49 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 100 (accept_3_3 35 49 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 100 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 49 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 100 (accept_3_3 32 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 100 (Polychromatic418967fa.accept_19_12_11_5_1_950 31 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 100 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 49 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 100 (accept_3_3 29 49 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 100 (Polychromatic418967fa.accept_11_6_5_1_1_586 28 49 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 100 (accept_3_3 26 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 100 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 100 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 100 (accept_3_3 23 49 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 100 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 49 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 100 (accept_3_3 20 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 100 (Polychromatic418967fa.accept_13_6_10_9_1_4329 19 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 100 (Polychromatic418967fa.accept_22_18_5_12_1_4337 18 49 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 100 (accept_3_3 17 49 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 100 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 49 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 100 (accept_3_3 14 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 100 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 100 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 49 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 100 (accept_3_3 11 49 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 100 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 49 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 100 (accept_3_3 8 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  100 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 100 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 49 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 100 (accept_3_3 5 49 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 100 (Polychromatic418967fa.accept_18_4_13_10_1_2064 4 49 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 49
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 100 (accept_3_3 2 49 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 100 (Polychromatic418967fa.accept_13_1_10_9_1_215 1
  49 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  100))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 100 (allA_succ_of_accept 47 48 100 (accept_3_3 47
  48 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 100 2 23 24 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 100
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 48 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 100 4 11 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 48 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 100 2 21 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 100 (accept_3_3 41 48 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 100 4 10 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 100 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 48 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 100 2 19 24 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 100
  (Polychromatic418967fa.accept_15_7_3_10_1_817 37 48 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 100 4 9 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 100 (accept_3_3 35 48 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48
  100 2 17 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  48 100 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 48 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 48 100 4 8 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 48 100 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 48 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 100 2 15 24 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 100 (accept_3_3 29 48 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 100 4 7 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 100 (Polychromatic418967fa.accept_18_9_12_10_1_387 27 48 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 100 2 13 24 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 100
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 48 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 100 4 6 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 100 (accept_3_3 23 48 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48
  100 2 11 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  48 100 (Polychromatic418967fa.accept_15_6_3_10_1_2341 21 48 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 48 100 4 5 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 48 100 (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 48 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 100 2 9 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 100 (accept_3_3 17 48 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 100 4 4 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 48 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 48 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 100 2 7 24 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 100
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 48 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 100 4 3 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 100 (accept_3_3 11 48 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48
  100 2 5 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  48 100 (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 48 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 48 100 4 2 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 48 100 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 100 2 3 24 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 100 (accept_3_3 5 48 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 100 4 1 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 48 100 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 100 2 1 24 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 100
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 48 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 100)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 100 (allA_of_3_1 47 47 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 46 100 (allA_succ_of_accept 45 46 100
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 45 46 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 100 2 22 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 46 100 (Polychromatic418967fa.accept_11_10_2_1_1_1036 43 46 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 100 2 21 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 100 (accept_3_3 41 46 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 100 2 20 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 100 (Polychromatic418967fa.accept_15_9_1_10_1_4316 39 46 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 100 2 19 23 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 100
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 46 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 100 2 18 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 100 (accept_3_3 35 46 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46
  100 2 17 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  46 100 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 46 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 46 100 2 16 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 46 100 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 46 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 100 2 15 23 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 100 (accept_3_3 29 46 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 100 2 14 23 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 100
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 46 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 46 100 2 13 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 46 100 (Polychromatic418967fa.accept_11_3_2_1_1_994 25 46 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 100 2 12 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 100 (accept_3_3 23 46 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 100 2 11 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 100 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 46 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 100 2 10 23 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 100
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 46 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 100 2 9 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 100 (accept_3_3 17 46 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  100 2 8 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 100 (Polychromatic418967fa.accept_13_2_7_9_1_2616 15 46 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 100 2 7 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 46 100 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 46 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 100 2 6 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 100 (accept_3_3 11 46 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 100 2 5 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 46 100 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 46 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 100 2 4 23 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 100
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 46 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 46 100 2 3 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 46 100 (accept_3_3 5 46 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 100
  2 2 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46
  100 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 46 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 46 100 2 1 23 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 46 100 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 46 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 46 100)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 100
  (allA_succ_of_accept 44 45 100 (accept_3_3 44 45 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  45 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 45 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 45 100 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 45 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 100 (accept_3_3 41 45 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 100 5 8 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 45 100 (Polychromatic418967fa.accept_16_7_13_4_1_1348 39 45 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 100 (accept_3_3 38 45 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 100
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 45 100 5 7 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 45 100 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 45 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 100 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 45 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 100 (accept_3_3 32 45 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  45 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 100 5 6 9 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 100 (accept_3_3 29
  45 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 100
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 28 45 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 45 100 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 45 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 100 (accept_3_3 26 45 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 45 100 5 5 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 45 100 (Polychromatic418967fa.accept_16_8_13_4_1_3258 24 45 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 100 (accept_3_3 23 45 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 100 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 45 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 100
  (Polychromatic418967fa.accept_17_4_11_15_1_3170 21 45 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 45 100 5 4 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 45 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 45 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 100 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 45 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 100 (accept_3_3 17 45 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 100 (Polychromatic418967fa.accept_13_3_6_9_1_1150
  16 45 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 100 5 3 9 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 100 (accept_3_3 14
  45 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 100
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 100 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 100 (accept_3_3 11 45 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 45 100 5 2 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 45 100 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 45 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 100 (accept_3_3 8 45 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 45 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 100
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 45 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 45 100 5 1 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 45 100 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 45 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 100 (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 45 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 100 (accept_3_3 2 45 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  100))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 100 (allA_of_3_1 44 44 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 43 100 (allA_succ_of_accept 42 43 100 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 43 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 100 (accept_3_3 41 43 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 100 (Polychromatic418967fa.accept_9_4_7_1_1_379 40
  43 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 100 (accept_3_3 38 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 100 (Polychromatic418967fa.accept_27_10_16_19_1_4336 37 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 100 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 43 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 100 (accept_3_3 35 43 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 100 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 43 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 100 (accept_3_3 32 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 100 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 100 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 43 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 100 (accept_3_3 29 43 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 100 (Polychromatic418967fa.accept_16_12_11_4_1_1359 28 43 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 100 (accept_3_3 26 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 100 (Polychromatic418967fa.accept_16_9_11_4_1_3194 25 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 100 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 43 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 100 (accept_3_3 23 43 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 100 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 43 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 100 (accept_3_3 20 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 100 (Polychromatic418967fa.accept_13_6_4_9_1_4326 19 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 100 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 43 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 100 (accept_3_3 17 43 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 100 (Polychromatic418967fa.accept_15_1_13_10_1_1507 16 43 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 100 (accept_3_3 14 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 100 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 100 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 43 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 100 (accept_3_3 11 43 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 100 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 43 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 100 (accept_3_3 8 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  100 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 100 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 43 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 100 (accept_3_3 5 43 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 100 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 43 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 100 (accept_3_3 2 43 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 100 (Polychromatic418967fa.accept_15_1_13_10_1_1507
  1 43 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  100))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 100 (allA_succ_of_accept 41 42 100 (accept_3_3 41 42 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 100 2 20 21 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 100
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 42 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 100 2 19 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 100 (Polychromatic418967fa.accept_15_7_12_10_1_4335 37 42 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 100 2 18 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 100 (accept_3_3 35 42 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 100 2 17 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 100 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 42 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 100 2 16 21 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 100
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 42 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 100 2 15 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 100 (accept_3_3 29 42 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42
  100 2 14 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  42 100 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 42 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 42 100 2 13 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 42 100 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 42 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 100 2 12 21 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 100 (accept_3_3 23 42 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 100 2 11 21 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 100
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 42 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 100 2 10 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 100 (Polychromatic418967fa.accept_13_6_3_9_1_1827 19 42 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 100 2 9 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 100 (accept_3_3 17 42 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 100 2 8 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 100 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 42 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 100 2 7 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 100 (Polychromatic418967fa.accept_9_4_6_1_1_393 13
  42 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 100 2 6 21 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 100 (accept_3_3 11
  42 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 100 2 5 21 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 100
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 42 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 100 2 4 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 100 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 42 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 100 2 3 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 100 (accept_3_3 5 42 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 100 2 2 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 100 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 42 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 100 2 1 21 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 100 (Polychromatic418967fa.accept_19_1_4_5_1_4313 1
  42 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  100)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 100 (allA_of_3_1 41 41 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 100 (allA_succ_of_accept 39 40 100 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 40 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 100 2 19 20 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 100
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 37 40 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 40 100 4 9 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 40 100 5 7 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 40 100 2 17 20 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 40 100 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 40 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 100 4 8 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 100 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 40 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 100 10 3 4 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 100 (accept_3_3 29 40 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40 100 4 7 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 40 100 (Polychromatic418967fa.accept_16_11_8_4_1_2234
  27 40 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 100 2 13 20 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 40 100 5 5 8 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 40 100 4 6 10 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 100 (accept_3_3 23
  40 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 100 2 11 20 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 100
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 40 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 100 20 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 100 (Polychromatic418967fa.accept_13_6_1_9_1_619 19 40 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 100 2 9 20 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 100 (accept_3_3 17 40 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 100 4 4 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 40 100 5 3 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 40 100 2 7 20 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 40 100 (Polychromatic418967fa.accept_16_13_8_4_1_3250 13 40 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 100 4 3 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 100 (accept_3_3 11 40 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 100 10 1 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 40 100 (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 40 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 100 4 2 10 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 100
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 40 100 2 3 20 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 40 100 5 1 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 40 100 4 1 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 40 100 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 40 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 100 2 1 20 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 100 (Polychromatic418967fa.accept_16_1_8_4_1_4334 1 40 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 100))))))))))))))))))))))))))))))))))))))))
  (allB_succ 39 100 (allA_succ_of_accept 38 39 100 (accept_3_3 38 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 39 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 100 (Polychromatic418967fa.accept_21_15_18_16_1_2942 36 39
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 100 (accept_3_3 35 39 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 100 (Polychromatic418967fa.accept_7_6_4_2_1_236 34
  39 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 100
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 39 100 (accept_3_3 32 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  39 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 39 100 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 39 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 100 (accept_3_3 29 39 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 100 (Polychromatic418967fa.accept_16_12_7_4_1_687 28 39 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 100
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 100 (accept_3_3 26 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  39 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 100 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 39 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 100 (accept_3_3 23 39 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 100 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 39 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 100
  (Polychromatic418967fa.accept_22_21_17_12_1_4333 21 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 39 100 (accept_3_3 20 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 100 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 39 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 100 (accept_3_3 17 39 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 100 (Polychromatic418967fa.accept_9_7_3_1_1_386 16
  39 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 100
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 100 (accept_3_3 14 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  39 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 39 100 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 39 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 100 (accept_3_3 11 39 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 100 (Polychromatic418967fa.accept_17_10_5_15_1_4332 10 39 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 100
  (Polychromatic418967fa.accept_14_9_11_2_1_2501 9 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 100 (accept_3_3 8 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 100 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 39 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 100 (accept_3_3 5 39 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 100 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 39 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 100 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 39
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 100 (accept_3_3 2 39 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 39
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  100))))))))))))))))))))))))))))))))))))))) (allB_succ 38 100 (allA_of_3_1 38 38 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 100 (allA_succ_of_accept 36 37 100 (Polychromatic418967fa.accept_19_17_18_5_1_3012 36 37 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 100 (accept_3_3 35 37 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 100 (Polychromatic418967fa.accept_12_10_1_4_1_392
  34 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 100 (accept_3_3 32 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 100 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 100 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 37 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 100 (accept_3_3 29 37 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 100 (Polychromatic418967fa.accept_13_2_11_9_1_591 28 37 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 100 (accept_3_3 26 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 100 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 100 (Polychromatic418967fa.accept_16_8_5_4_1_674 24 37 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 100 (accept_3_3 23 37 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 100 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 37 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 100 (accept_3_3 20 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 100 (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 100 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 37 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 100 (accept_3_3 17 37 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 100 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 37 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 100 (accept_3_3 14 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 100 (Polychromatic418967fa.accept_18_13_1_10_1_4331 13 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 100 (Polychromatic418967fa.accept_15_12_7_10_1_3297 12 37 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 100 (accept_3_3 11 37 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 100 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 37 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 100 (accept_3_3 8 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  100 (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 37 100 (Polychromatic418967fa.accept_16_6_5_4_1_4330 6 37 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 100 (accept_3_3 5 37 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 100 (Polychromatic418967fa.accept_14_4_9_2_1_95 4 37 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 100 (accept_3_3 2 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37
  100 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 37 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 37 100))))))))))))))))))))))))))))))))))))) (allB_succ 36 100 (allA_succ_of_accept 35 36 100 (accept_3_3 35
  36 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 100 2 17 18 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 100
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 36 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 36 100 4 8 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 100 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 36 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 100 2 15 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 100 (accept_3_3 29 36 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 100 4 7 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 36 100 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 36 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 100 2 13 18 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 100
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 25 36 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 100 4 6 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 100 (accept_3_3 23 36 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36
  100 2 11 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  36 100 (Polychromatic418967fa.accept_17_4_2_15_1_1254 21 36 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 36 100 4 5 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 36 100 (Polychromatic418967fa.accept_13_6_10_9_1_4329 19 36 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 100 2 9 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 100 (accept_3_3 17 36 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 100 4 4 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 36 100 (Polychromatic418967fa.accept_14_1_8_2_1_1675 15 36 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 100 2 7 18 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 100
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 36 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 100 4 3 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 100 (accept_3_3 11 36 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36
  100 2 5 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  36 100 (Polychromatic418967fa.accept_21_9_15_16_1_4328 9 36 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 36 100 4 2 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 36 100 (Polychromatic418967fa.accept_17_7_2_15_1_1255 7 36 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 100 2 3 18 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 100 (accept_3_3 5 36 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 100 4 1 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 36 100 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 36 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 100 2 1 18 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 100
  (Polychromatic418967fa.accept_13_1_10_9_1_215 1 36 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 100)))))))))))))))))))))))))))))))))))) (allB_succ 35 100 (allA_of_3_1 35 35 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 34 100 (allA_succ_of_accept 33 34 100 (Polychromatic418967fa.accept_9_6_7_1_1_145 33
  34 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 34 100 2 16 17 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 34 100
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 34 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 34 100 2 15 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 34 100 (accept_3_3 29 34 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34
  100 2 14 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  34 100 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 34 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 34 100 2 13 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 34 100 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 34 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 100 2 12 17 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 100 (accept_3_3 23 34 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 100 2 11 17 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 100
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 34 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 100 2 10 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 100 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 34 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 100 2 9 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 100 (accept_3_3 17 34 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 100 2 8 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 34 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 100 2 7 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 100 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  34 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 100 2 6 17 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 100 (accept_3_3 11
  34 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 100 2 5 17 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 100
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 34 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 100 2 4 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 100 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 34 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 100 2 3 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 100 (accept_3_3 5 34 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 100 2 2 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 100 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 34 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 100 2 1 17 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 34
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 100))))))))))))))))))))))))))))))))))
  (allB_succ 33 100 (allA_succ_of_accept 32 33 100 (accept_3_3 32 33 100 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 33 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 100 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 33 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 100 (accept_3_3 29 33 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 100 (Polychromatic418967fa.accept_13_2_7_9_1_2616
  28 33 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 100
  (Polychromatic418967fa.accept_18_9_15_10_1_395 27 33 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 100 (accept_3_3 26 33 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 100 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 33 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 100 (accept_3_3 23 33 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 100 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 33 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 100
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 100 (accept_3_3 20 33 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 33 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 100 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 33 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 100 (accept_3_3 17 33 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 100 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 33 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 100
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 15 33 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 100 (accept_3_3 14 33 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 100 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 33 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 100 (accept_3_3 11 33 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 100 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 33 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 100
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 33 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 100 (accept_3_3 8 33 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 33 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 100 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 33 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 100 (accept_3_3 5 33 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 100 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 33 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 100 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 33
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 100 (accept_3_3 2 33 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 100)))))))))))))))))))))))))))))))))
  (allB_succ 32 100 (allA_of_3_1 32 32 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 100
  (allA_succ_of_accept 30 31 100 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 31 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 100 (accept_3_3 29 31 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 100 (Polychromatic418967fa.accept_13_2_5_9_1_610 28 31 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 27
  31 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 100 (accept_3_3 26 31
  100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 100
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 31 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 100 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 100 (accept_3_3 23 31 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 100 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 31 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  31 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 100 (accept_3_3 20 31
  100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 100
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 31 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 100 (Polychromatic418967fa.accept_27_18_4_19_1_4327 18 31 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 100 (accept_3_3 17 31 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 100 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 31 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 15
  31 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 100 (accept_3_3 14 31
  100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 100
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 31 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 31 100 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 31 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 100 (accept_3_3 11 31 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 31 100 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 31 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 31 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 100 (accept_3_3 8 31 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  100 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 31 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 100 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 31 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 100 (accept_3_3 5 31 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 100 (Polychromatic418967fa.accept_13_4_5_9_1_1829 4 31 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 100 (accept_3_3 2 31 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 100 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 31
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 100)))))))))))))))))))))))))))))))
  (allB_succ 30 100 (allA_succ_of_accept 29 30 100 (accept_3_3 29 30 100 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 100 2 14 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 30 100 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 30 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 100 2 13 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 30 100 5 5 6 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 30 100 2 12 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 100 (accept_3_3 23 30 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 100 2 11 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 100 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 30 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 100 10 2 3 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 100
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 19 30 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 100 2 9 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 100 (accept_3_3 17 30 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30
  100 2 8 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30
  100 5 3 6 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30
  100 2 7 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13
  30 100 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 30 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 30 100 2 6 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 30 100 (accept_3_3 11 30 100 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 100 10 1 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 100 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 30 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 100 2 4 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 100 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 30 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 100 2 3 15 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 100 5 1 6 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 30 100 2 2 15 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 100
  (Polychromatic418967fa.accept_12_3_6_4_1_400 3 30 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 30 100 2 1 15 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 100 (Polychromatic418967fa.accept_16_1_14_4_1_3220 1 30 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 100)))))))))))))))))))))))))))))) (allB_succ 29 100 (allA_of_3_1 29 29
  100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 100 (allA_succ_of_accept 27 28 100
  (Polychromatic418967fa.accept_11_5_6_1_1_988 27 28 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 100 2 13 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 100 (Polychromatic418967fa.accept_16_9_12_4_1_3255 25 28 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 100 4 6 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 100 (accept_3_3 23 28 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 28 100 2 11 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 28 100 (Polychromatic418967fa.accept_16_5_12_4_1_4325 21 28 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 100 4 5 7 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 100
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 28 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 100 2 9 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 100 (accept_3_3 17 28 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  100 4 4 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 100 (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 28 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 100 2 7 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 28 100 (Polychromatic418967fa.accept_16_13_12_4_1_4323 13 28 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 100 4 3 7 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 100 (accept_3_3 11 28 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 100 2 5 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 100 (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 28 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 100 4 2 7 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 100
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 28 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 28 100 2 3 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 28 100 (accept_3_3 5 28 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 100
  4 1 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 100
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 28 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 100 2 1 14 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 100 (Polychromatic418967fa.accept_13_1_2_9_1_1186 1 28 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 100)))))))))))))))))))))))))))) (allB_succ 27 100 (allA_succ_of_accept 26
  27 100 (accept_3_3 26 27 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 100
  (Polychromatic418967fa.accept_6_1_3_4_1_1 25 27 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 27 100 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 27 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 100 (accept_3_3 23 27 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 27 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 27 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 100 (Polychromatic418967fa.accept_13_8_1_9_1_1178
  21 27 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 100 (accept_3_3 20
  27 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 100
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 27 100 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 27 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 100 (accept_3_3 17 27 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 27 100 (Polychromatic418967fa.accept_19_16_8_5_1_4322 16 27 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 100
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 27 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 100 (accept_3_3 14 27 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 27 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 100 (Polychromatic418967fa.accept_16_12_11_4_1_1359 12 27 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 100 (accept_3_3 11 27 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 100 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 27 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 100
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 27 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 100 (accept_3_3 8 27 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 100 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 27 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 100 (accept_3_3 5 27 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 100 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 27 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 100 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 100 (accept_3_3 2 27 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 27
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 100)))))))))))))))))))))))))))
  (allB_succ 26 100 (allA_of_3_1 26 26 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 100
  (allA_succ_of_accept 24 25 100 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 25 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 100 (accept_3_3 23 25 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 100 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 25 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  25 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 100 5 4 5 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 100
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 25 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 100 (Polychromatic418967fa.accept_19_18_6_5_1_4321 18 25 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 100 (accept_3_3 17 25 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 100 (Polychromatic418967fa.accept_13_3_12_9_1_1193 16 25 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 25 100 5 3 5 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 25 100 (accept_3_3 14 25 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 100 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 25 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 100
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 25 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 100 (accept_3_3 11 25 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25
  100 5 2 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25
  100 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 100 (accept_3_3 8 25 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  100 (Polychromatic418967fa.accept_19_7_6_5_1_4320 7 25 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 100 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 25 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 25 100 5 1 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 25 100 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 25
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 100
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 25 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 100 (accept_3_3 2 25 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  100 (Polychromatic418967fa.accept_19_1_6_5_1_4319 1 25 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 25 100))))))))))))))))))))))))) (allB_succ 24 100 (allA_succ_of_accept 23 24 100 (accept_3_3 23
  24 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 100 2 11 12 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 100
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 100 4 5 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 100 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 24 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 100 2 9 12 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 100 (accept_3_3 17 24 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 100 4 4 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 100 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 24 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 100 2 7 12 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 100 (Polychromatic418967fa.accept_7_6_3_2_1_461 13
  24 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 100 4 3 6 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 100 (accept_3_3 11
  24 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 100 2 5 12 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 100
  (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 24 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 100 4 2 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 100 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 100 2 3 12 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 100 (accept_3_3 5 24 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 24 100 4 1 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 24 100 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 100 2 1 12 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 100 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 24
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 100)))))))))))))))))))))))) (allB_succ
  23 100 (allA_of_3_1 23 23 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 100 (allA_succ_of_accept 21 22
  100 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 22 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 100 2 10 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 100 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 22 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 100 2 9 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 100 (accept_3_3 17 22 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 100 2 8 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 100 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 22 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 100 2 7 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 100 (Polychromatic418967fa.accept_7_6_1_2_1_230 13
  22 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 100 2 6 11 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 100 (accept_3_3 11
  22 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 100 2 5 11 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 100
  (Polychromatic418967fa.accept_23_9_22_8_1_4318 9 22 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 100 2 4 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 100 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 22 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 100 2 3 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 100 (accept_3_3 5 22 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 100 2 2 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 100 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 22 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 100 2 1 11 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 100 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  22 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 100)))))))))))))))))))))) (allB_succ
  21 100 (allA_succ_of_accept 20 21 100 (accept_3_3 20 21 100 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 21 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 100 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 21 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 100 (accept_3_3 17 21 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 100 (Polychromatic418967fa.accept_9_7_3_1_1_386 16
  21 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 100
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 21 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 100 (accept_3_3 14 21 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 100 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 21 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 100 (accept_3_3 11 21 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 100 (Polychromatic418967fa.accept_17_10_4_15_1_2165 10 21
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 100
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 21 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 100 (accept_3_3 8 21 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 21 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 100 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 21 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 100 (accept_3_3 5 21 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 100 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 21 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 100 (Polychromatic418967fa.accept_13_3_8_9_1_1134 3
  21 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 100 (accept_3_3 2 21 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 100))))))))))))))))))))) (allB_succ 20
  100 (allA_of_3_1 20 20 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 100 (allA_succ_of_accept 18 19 100
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 19 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 100 (accept_3_3 17 19 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 100 (Polychromatic418967fa.accept_13_3_6_9_1_1150 16 19 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 100 (accept_3_3 14 19 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 100 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 19 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 100
  (Polychromatic418967fa.accept_16_12_3_4_1_4317 12 19 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 100 (accept_3_3 11 19 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 100 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 19 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 19 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 100 (accept_3_3 8 19 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 100 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 19 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 100
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 6 19 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 100 (accept_3_3 5 19 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  100 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 19 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 100 (accept_3_3 2 19 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 100 (Polychromatic418967fa.accept_13_1_6_9_1_1197 1 19 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 100))))))))))))))))))) (allB_succ 18 100 (allA_succ_of_accept 17
  18 100 (accept_3_3 17 18 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 100 2 8 9 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 100
  (Polychromatic418967fa.accept_12_3_6_4_1_400 15 18 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 100 2 7 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 100 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 18 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 100 2 6 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 100 (accept_3_3 11 18 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 100 2 5 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 100 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 18 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 100 2 4 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 100 (Polychromatic418967fa.accept_15_7_3_10_1_817 7
  18 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 100 2 3 9 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 100 (accept_3_3 5 18
  100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 100 2 2 9 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 100
  (Polychromatic418967fa.accept_12_3_6_4_1_400 3 18 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 100 2 1 9 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 100 (Polychromatic418967fa.accept_13_1_5_9_1_226 1 18 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 100)))))))))))))))))) (allB_succ 17 100 (allA_of_3_1 17 17 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 100 (allA_succ_of_accept 15 16 100
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 16 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 100 2 7 8 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 100 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 16 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 100 4 3 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 100 (accept_3_3 11 16 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 100 2 5 8 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 100 (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 16 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 100 4 2 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 100 (Polychromatic418967fa.accept_13_7_3_9_1_1142 7
  16 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 100 2 3 8 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 100 (accept_3_3 5 16
  100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 100 4 1 4 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 100
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 16 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 100 2 1 8 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 100 (Polychromatic418967fa.accept_17_1_16_15_1_4315 1 16 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 100)))))))))))))))) (allB_succ 15 100 (allA_succ_of_accept 14 15 100
  (accept_3_3 14 15 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 100
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 15 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 100 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 15 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 100 (accept_3_3 11 15 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 15 100 5 2 3 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 15 100 (Polychromatic418967fa.accept_18_9_15_10_1_395 9 15 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 100 (accept_3_3 8 15 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 100
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 15 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 15 100 5 1 3 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 15 100 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 15 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 100 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 15 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 100 (accept_3_3 2 15 100
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 15
  100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 100))))))))))))))) (allB_succ 14 100
  (allA_of_3_1 14 14 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 100 (allA_succ_of_accept 12 13 100
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 13 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 100 (accept_3_3 11 13 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 100 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 13 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 100 (accept_3_3 8 13 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 100 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 13 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 100
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 13 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 100 (accept_3_3 5 13 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  100 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 13 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 13 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 100 (accept_3_3 2 13 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 13 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 100))))))))))))) (allB_succ 12 100 (allA_succ_of_accept 11 12
  100 (accept_3_3 11 12 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 100 2 5 6 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 100
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 12 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 100 4 2 3 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 100 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 12 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 100 2 3 6 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 100 (accept_3_3 5 12 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 12 100 4 1 3 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 12 100 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 100 2 1 6 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 100 (Polychromatic418967fa.accept_16_1_12_4_1_695 1
  12 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 100)))))))))))) (allB_succ 11 100
  (allA_of_3_1 11 11 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 100 (allA_succ_of_accept 9 10 100
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 10 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 100 2 4 5 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 100 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 10 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 100 2 3 5 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 10 100 5 1 2 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 10 100 2 2 5 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 100 (Polychromatic418967fa.accept_19_3_10_5_1_4314 3 10 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 100 2 1 5 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 100
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 10 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 100)))))))))) (allB_succ 9 100 (allA_succ_of_accept 8 9 100 (accept_3_3 8 9 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 9 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 100
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 9 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 100 (accept_3_3 5 9 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 100
  (Polychromatic418967fa.accept_14_4_9_2_1_95 4 9 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 100 (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 9 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 100 (accept_3_3 2 9 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 100))))))))) (allB_succ 8 100 (allA_of_3_1 8 8 100 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 100 (allA_succ_of_accept 6 7 100
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 7 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 100 (accept_3_3 5 7 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 100
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 7 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 100 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 100 (accept_3_3 2 7 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 100 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 7 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 100))))))) (allB_succ 6 100 (allA_succ_of_accept 5 6 100
  (accept_3_3 5 6 100 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 100 2 2 3 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 100
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 6 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 100 2 1 3 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 100 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 6 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 100)))))) (allB_succ 5 100 (allA_of_3_1 5 5 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 100 (allA_succ_of_accept 3 4 100 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 4 100
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 100 2 1 2 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 100
  (Polychromatic418967fa.accept_19_1_4_5_1_4313 1 4 100 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 100)))) (allB_succ 3 100 (allA_succ_of_accept 2 3 100 (accept_3_3 2 3 100 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 100 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 3 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 100))) (allB_succ 2 100 (allA_of_3_1 2 2 100 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  100))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


