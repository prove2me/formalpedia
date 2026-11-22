-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch82
-- name    : Polychromatic418967fa_Branch82
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:09:03.601149+00:00
-- url     : https://prove2.me/theorems/742f2dd5-315c-48e1-8e6e-4af6ddb24790
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

def Polychromatic418967fa.branch_82 : allB 82 82 :=
  allB_succ' 2 81 82 (Eq.refl Bool.true) (allA_succ_of_accept 1 81 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 82)) (allB_succ' 3 80 82 (Eq.refl Bool.true)
  (allA_of_3_1 3 80 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 79 82 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 79 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 82 (accept_3_3 2 79 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 82)))) (allB_succ' 5 78 82 (Eq.refl Bool.true) (allA_succ_of_gcd
  4 78 82 2 2 39 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 78 82 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 78 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 78 82 2 1 39 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 78 82 (Polychromatic418967fa.accept_17_1_10_14_1_1173 1 78 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 82))))) (allB_succ' 6 77 82 (Eq.refl Bool.true) (allA_of_3_1 6
  77 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 76 82 (Eq.refl Bool.true) (allA_succ_of_gcd 6 76 82 2 3
  38 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 82
  (accept_3_3 5 76 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 82 2 2 38 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76 82
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 76 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 82 2 1 38 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 82 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 76 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76 82))))))) (allB_succ' 8 75 82 (Eq.refl Bool.true) (allA_succ_of_accept 7
  75 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 75 82 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 75 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 82 (accept_3_3 5 75 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 75 82 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 75 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 82 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 75
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 82 (accept_3_3 2 75 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 82)))))))) (allB_succ' 9 74 82 (Eq.refl
  Bool.true) (allA_of_3_1 9 74 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 73 82 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 73 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 82 (accept_3_3 8 73 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 73 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 82 (Polychromatic418967fa.accept_15_6_13_7_1_222 6
  73 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 82 (accept_3_3 5 73 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73 82 (Polychromatic418967fa.accept_12_4_1_10_1_221 4
  73 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 82
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 73 82 (accept_3_3 2 73 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 82
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 73 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 73 82)))))))))) (allB_succ' 11 72 82 (Eq.refl Bool.true) (allA_succ_of_gcd 10 72 82 2 5 36 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 82
  (Polychromatic418967fa.accept_13_9_7_4_1_953 9 72 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 82 2 4 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 82 (Polychromatic418967fa.accept_14_7_2_12_1_1430 7 72 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 82 2 3 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 82 (accept_3_3 5 72 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 82 2 2 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 82 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 82 2 1 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 82 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1
  72 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 82))))))))))) (allB_succ' 12 71 82
  (Eq.refl Bool.true) (allA_of_3_1 12 71 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 70 82 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 70 82 2 6 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 70 82 (accept_3_3 11 70 82 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 70 82 2 5 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 70 82 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 70 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 82 2 4 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 70 82 (Polychromatic418967fa.accept_19_7_13_6_1_1914 7 70 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 82 2 3 35 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 82 (accept_3_3 5 70 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 82 2 2 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70 82 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 70 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 82 2 1 35 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 82
  (Polychromatic418967fa.accept_13_1_5_4_1_463 1 70 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 82))))))))))))) (allB_succ' 14 69 82 (Eq.refl Bool.true) (allA_succ_of_accept 13 69 82
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 69 82 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 69 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 82 (accept_3_3 11 69 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 69 82 (Polychromatic418967fa.accept_17_10_1_14_1_489 10 69 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 82 (Polychromatic418967fa.accept_18_9_15_10_1_395 9
  69 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 82 (accept_3_3 8 69 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 82
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 69 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 82 (accept_3_3 5 69 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 82
  (Polychromatic418967fa.accept_7_4_6_5_1_141 4 69 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 69 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 82 (accept_3_3 2 69 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 69 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69 82)))))))))))))) (allB_succ' 15 68 82 (Eq.refl Bool.true)
  (allA_of_3_1 15 68 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 67 82 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 67 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 82 (accept_3_3 14 67 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 67 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 82 (Polychromatic418967fa.accept_9_3_4_1_1_22 12
  67 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 82 (accept_3_3 11 67 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 82 (Polychromatic418967fa.accept_21_10_4_19_1_3136
  10 67 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 82
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 82 (accept_3_3 8 67 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 82
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 67 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 67 82 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 67 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 82 (accept_3_3 5 67 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 67 82 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 67 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 82 (accept_3_3 2 67 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 82)))))))))))))))) (allB_succ' 17 66 82
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 66 82 2 8 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 66 82 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 66 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 82 2 7 33 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 82
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 66 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 66 82 2 6 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 66 82 (accept_3_3 11 66 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 82
  2 5 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 82
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 66 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 82 2 4 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 82 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 66 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 82 2 3 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 82 (accept_3_3 5 66 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 66 82 2 2 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 66 82 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 66 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 82 2 1 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 82 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 66
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66 82))))))))))))))))) (allB_succ' 18 65 82
  (Eq.refl Bool.true) (allA_of_3_1 18 65 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 64 82 (Eq.refl
  Bool.true) (allA_succ_of_gcd 18 64 82 2 9 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 64 82 (accept_3_3 17 64 82 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 64 82 2 8 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 64 82 (Polychromatic418967fa.accept_13_2_12_4_1_943 15 64 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 82 2 7 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 82 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 64 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 82 2 6 32 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 82 (accept_3_3 11 64 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 82 2 5 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 82 (Polychromatic418967fa.accept_20_9_4_2_1_1900 9
  64 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 82 2 4 32 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 82
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 64 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 64 82 2 3 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 64 82 (accept_3_3 5 64 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 82 2
  2 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64 82
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 64 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 64 82 2 1 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 64 82 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 64 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 64 82))))))))))))))))))) (allB_succ' 20 63 82 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 63 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 82 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 63 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 82 (accept_3_3 17 63 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 82 (Polychromatic418967fa.accept_14_2_7_12_1_1485
  16 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 82
  (Polychromatic418967fa.accept_10_5_3_2_1_899 15 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 82 (accept_3_3 14 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63
  82 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 63 82 (Polychromatic418967fa.accept_13_12_11_4_1_3111 12 63 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 82 (accept_3_3 11 63 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 63 82 (Polychromatic418967fa.accept_13_10_11_4_1_2248 10 63 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 82 (accept_3_3 8 63 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 82
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 82 (accept_3_3 5 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 82
  (Polychromatic418967fa.accept_15_4_3_7_1_713 4 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 63 82 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 63 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 82 (accept_3_3 2 63 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 63 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 82)))))))))))))))))))) (allB_succ' 21 62 82 (Eq.refl Bool.true)
  (allA_of_3_1 21 62 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 61 82 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 61 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 82 (accept_3_3 20 61 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 61 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 82 (Polychromatic418967fa.accept_13_5_9_4_1_441 18
  61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 82 (accept_3_3 17 61 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 61 82 (Polychromatic418967fa.accept_10_6_1_2_1_874 16
  61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 82
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 61 82 (accept_3_3 14 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61
  82 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 61 82 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 61 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 82 (accept_3_3 11 61 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 61 82 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 61 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 82 (accept_3_3 8 61 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 82
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 82 (accept_3_3 5 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 82
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 82 (accept_3_3 2 61 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 82 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 61 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 82)))))))))))))))))))))) (allB_succ' 23 60 82 (Eq.refl
  Bool.true) (allA_succ_of_gcd 22 60 82 2 11 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 60 82 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 60 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 82 2 10 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 82 (Polychromatic418967fa.accept_27_19_6_1_1_3135
  19 60 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 82 2 9 30 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 82 (accept_3_3 17 60
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 82 2 8 30 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 82
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 60 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 60 82 2 7 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 60 82 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 60 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 82 2 6 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 82 (accept_3_3 11 60 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 60 82 2 5 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 60 82 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 82 2 4 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 82 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 60
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 82 2 3 30 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 82 (accept_3_3 5 60
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 82 2 2 30 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 82
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 60 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 82 2 1 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 82 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 60 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 82))))))))))))))))))))))) (allB_succ' 24 59 82 (Eq.refl Bool.true)
  (allA_of_3_1 24 59 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 58 82 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 58 82 2 12 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 58 82 (accept_3_3 23 58 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 82
  2 11 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58
  82 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 58 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 82 2 10 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 82 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 58 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 82 2 9 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 82 (accept_3_3 17 58 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 82 2 8 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 82 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 58 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 82 2 7 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 82 (Polychromatic418967fa.accept_18_13_4_10_1_1076
  13 58 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 82 2 6 29 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 82 (accept_3_3 11 58
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 82 2 5 29 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 82
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 58 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 82 2 4 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 82 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 58 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 82 2 3 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 82 (accept_3_3 5 58 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 82 2 2 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 82 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 58 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 82 2 1 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 82 (Polychromatic418967fa.accept_21_1_16_19_1_3134 1
  58 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 82)))))))))))))))))))))))))
  (allB_succ' 26 57 82 (Eq.refl Bool.true) (allA_succ_of_accept 25 57 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 82
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 82 (accept_3_3 23 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57
  82 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 57 82 (Polychromatic418967fa.accept_15_6_12_7_1_1360 21 57 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 82 (accept_3_3 20 57 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 57 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 82 (Polychromatic418967fa.accept_7_4_1_5_1_540 18
  57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 82 (accept_3_3 17 57 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 82 (Polychromatic418967fa.accept_9_7_3_1_1_386 16
  57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 82
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 82 (accept_3_3 14 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57
  82 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 82 (Polychromatic418967fa.accept_13_12_5_4_1_3133 12 57 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 82 (accept_3_3 11 57 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 57 82 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 57 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 82 (Polychromatic418967fa.accept_10_9_7_2_1_887 9
  57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 82 (accept_3_3 8 57 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 82
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 82 (accept_3_3 5 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 82
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 82 (accept_3_3 2 57 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 82)))))))))))))))))))))))))) (allB_succ' 27 56 82 (Eq.refl
  Bool.true) (allA_of_3_1 27 56 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 55 82 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 55 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 82 (accept_3_3 26 55 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 55 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 82 (Polychromatic418967fa.accept_17_7_4_14_1_2106
  24 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 82 (accept_3_3 23 55
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 82 (Polychromatic418967fa.accept_7_1_6_5_1_39
  22 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 82
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 82 (accept_3_3 20 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55
  82 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 82 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 55 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 82 (accept_3_3 17 55 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 82 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 55 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 82
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 82 (accept_3_3 14 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55
  82 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 55 82 (Polychromatic418967fa.accept_13_12_3_4_1_928 12 55 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 82 (accept_3_3 11 55 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 55 82 (Polychromatic418967fa.accept_20_10_15_2_1_3132 10 55 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 82 (accept_3_3 8 55 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 82 (Polychromatic418967fa.accept_10_7_5_2_1_880 7
  55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 82
  (Polychromatic418967fa.accept_14_6_13_12_1_810 6 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 82 (accept_3_3 5 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 82
  (Polychromatic418967fa.accept_7_4_6_5_1_141 4 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 82 (accept_3_3 2 55 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 82)))))))))))))))))))))))))))) (allB_succ' 29 54 82 (Eq.refl
  Bool.true) (allA_succ_of_gcd 28 54 82 2 14 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 54 82 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 54 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 82 2 13 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 82 (Polychromatic418967fa.accept_13_12_2_4_1_3131
  25 54 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 82 2 12 27 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 82 (accept_3_3 23 54
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 82 2 11 27 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 82
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 54 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 82 2 10 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 54 82 (Polychromatic418967fa.accept_13_6_2_4_1_923 19 54 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 82 2 9 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 82 (accept_3_3 17 54 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 54 82 2 8 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 54 82 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 54 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 82 2 7 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 82 (Polychromatic418967fa.accept_15_13_9_7_1_2194
  13 54 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 82 2 6 27 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 82 (accept_3_3 11 54
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 82 2 5 27 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 54 82
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 54 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 54 82 2 4 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 82 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 54 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 82 2 3 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 82 (accept_3_3 5 54 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 54 82 2 2 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 54 82 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 54 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 82 2 1 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 82 (Polychromatic418967fa.accept_15_1_9_7_1_3130 1
  54 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 82)))))))))))))))))))))))))))))
  (allB_succ' 30 53 82 (Eq.refl Bool.true) (allA_of_3_1 30 53 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31
  52 82 (Eq.refl Bool.true) (allA_succ_of_gcd 30 52 82 2 15 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 82 (accept_3_3 29 52 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 52 82 2 14 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 52 82 (Polychromatic418967fa.accept_17_10_1_14_1_489 27 52 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 82 2 13 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 82 (Polychromatic418967fa.accept_11_3_8_5_1_336 25
  52 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 82 2 12 26 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 82 (accept_3_3 23 52
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 82 2 11 26 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 82
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 52 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 52 82 2 10 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 52 82 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 52 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 82 2 9 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 82 (accept_3_3 17 52 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 52 82 2 8 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 52 82 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 52 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 82 2 7 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 82 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  52 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 82 2 6 26 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 82 (accept_3_3 11 52
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 82 2 5 26 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 52 82
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 52 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 52 82 2 4 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 52 82 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 52 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 82 2 3 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 82 (accept_3_3 5 52 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 52 82 2 2 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 52 82 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 52 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 82 2 1 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 82 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 52
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 82)))))))))))))))))))))))))))))))
  (allB_succ' 32 51 82 (Eq.refl Bool.true) (allA_succ_of_accept 31 51 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 82
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 82 (accept_3_3 29 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51
  82 (Polychromatic418967fa.accept_13_2_12_4_1_943 28 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 51 82 (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 51 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 82 (accept_3_3 26 51 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 51 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 82 (Polychromatic418967fa.accept_7_3_2_5_1_147 24
  51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 82 (accept_3_3 23 51 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 82 (Polychromatic418967fa.accept_9_4_6_1_1_393 22
  51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 82
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 82 (accept_3_3 20 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51
  82 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 51 82 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 51 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 82 (accept_3_3 17 51 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 51 82 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 51 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 82 (Polychromatic418967fa.accept_13_2_12_4_1_943
  15 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 82 (accept_3_3 14 51
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 13
  51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 82
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 82 (accept_3_3 11 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51
  82 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 51 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 82 (accept_3_3 8 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 82 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 51 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 82 (accept_3_3 5 51 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 82 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 51 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 82
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 51 82 (accept_3_3 2 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 82
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 82)))))))))))))))))))))))))))))))) (allB_succ' 33 50 82 (Eq.refl Bool.true) (allA_of_3_1 33 50 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 49 82 (Eq.refl Bool.true) (allA_succ_of_accept 33 49 82
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 82 (accept_3_3 32 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49
  82 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 49 82 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 49 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 82 (accept_3_3 29 49 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 49 82 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 49 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 82 (accept_3_3 26 49 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 82 (Polychromatic418967fa.accept_9_7_4_1_1_391 25
  49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 82
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 82 (accept_3_3 23 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49
  82 (Polychromatic418967fa.accept_16_6_1_2_1_3129 22 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 49 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 82 (accept_3_3 20 49 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 49 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 82 (Polychromatic418967fa.accept_13_5_10_4_1_1564
  18 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 82 (accept_3_3 17 49
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 82 (Polychromatic418967fa.accept_9_7_4_1_1_391
  16 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 82
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 82 (accept_3_3 14 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49
  82 (Polychromatic418967fa.accept_19_13_11_6_1_3128 13 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 82 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 49 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 82 (accept_3_3 11 49 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 82 (Polychromatic418967fa.accept_15_10_4_7_1_3127 10 49 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 82
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 82 (accept_3_3 8 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 82
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 82 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 49 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 82 (accept_3_3 5 49 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 82 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 49 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 82 (accept_3_3 2 49 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 82 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 49
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 82))))))))))))))))))))))))))))))))))
  (allB_succ' 35 48 82 (Eq.refl Bool.true) (allA_succ_of_gcd 34 48 82 2 17 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 82 (Polychromatic418967fa.accept_9_6_3_1_1_155 33
  48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 82 2 16 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 82
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 82 2 15 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 82 (accept_3_3 29 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 82
  2 14 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48
  82 (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 48 82 2 13 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 48 82 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 48 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 82 2 12 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 82 (accept_3_3 23 48 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 82 2 11 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 48 82 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 48 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 82 2 10 24 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 82
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 19 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 82 2 9 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 82 (accept_3_3 17 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 82
  2 8 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48
  82 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 48 82 2 7 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 82 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 48 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 82 2 6 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 82 (accept_3_3 11 48 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 48 82 2 5 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 48 82 (Polychromatic418967fa.accept_18_9_12_10_1_387 9 48 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 82 2 4 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 82 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 82 2 3 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 82 (accept_3_3 5 48
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 82 2 2 24 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48 82
  (Polychromatic418967fa.accept_21_3_6_19_1_3125 3 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 48 82 2 1 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 48 82 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 48 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 48 82))))))))))))))))))))))))))))))))))) (allB_succ' 36 47 82 (Eq.refl
  Bool.true) (allA_of_3_1 36 47 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 46 82 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 46 82 2 18 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 82 (accept_3_3 35 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 82
  2 17 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46
  82 (Polychromatic418967fa.accept_19_14_8_6_1_981 33 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 46 82 2 16 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 46 82 (Polychromatic418967fa.accept_10_1_6_2_1_867 31 46 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 82 2 15 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 82 (accept_3_3 29 46 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 46 82 2 14 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 46 82 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 46 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 82 2 13 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 82 (Polychromatic418967fa.accept_13_12_7_4_1_3124
  25 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 82 2 12 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 82 (accept_3_3 23 46
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 82 2 11 23 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 82
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 82 2 10 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 82 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 46 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 82 2 9 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 82 (accept_3_3 17 46 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 82 2 8 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 82 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 46 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 82 2 7 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 82 (Polychromatic418967fa.accept_7_6_4_5_1_314 13
  46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 82 2 6 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 82 (accept_3_3 11 46
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 82 2 5 23 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 82
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 82 2 4 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 82 (Polychromatic418967fa.accept_19_7_8_6_1_3123 7 46 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 82 2 3 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 82 (accept_3_3 5 46 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 82 2 2 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 82 (Polychromatic418967fa.accept_13_3_7_4_1_435 3 46 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 82 2 1 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 82 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 46
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 82)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 45 82 (Eq.refl Bool.true) (allA_succ_of_accept 37 45 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 82
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 82 (accept_3_3 35 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45
  82 (Polychromatic418967fa.accept_22_12_1_16_1_3122 34 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 82 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 45 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 82 (accept_3_3 32 45 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 82
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 82 (accept_3_3 29 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45
  82 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 45 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 82 (accept_3_3 26 45 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 45 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 82 (Polychromatic418967fa.accept_13_11_6_4_1_3121
  24 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 82 (accept_3_3 23 45
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 82 (Polychromatic418967fa.accept_7_1_3_5_1_33
  22 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 82
  (Polychromatic418967fa.accept_16_5_13_2_1_2138 21 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 45 82 (accept_3_3 20 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45
  82 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 45 82 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 45 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 82 (accept_3_3 17 45 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 45 82 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 45 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 82 (accept_3_3 14 45 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 82
  (Polychromatic418967fa.accept_17_12_11_14_1_3120 12 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 82 (accept_3_3 11 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45
  82 (Polychromatic418967fa.accept_13_10_6_4_1_1583 10 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 82 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 82 (accept_3_3 8 45 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 45 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 82 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6
  45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 82 (accept_3_3 5 45 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 82 (Polychromatic418967fa.accept_20_4_5_2_1_3119 4
  45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 82
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 45 82 (accept_3_3 2 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 82
  (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 82)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 44 82 (Eq.refl Bool.true) (allA_of_3_1 39 44 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 43 82 (Eq.refl Bool.true) (allA_succ_of_accept 39 43 82
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 82 (accept_3_3 38 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43
  82 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 43 82 (Polychromatic418967fa.accept_15_6_13_7_1_222 36 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 82 (accept_3_3 35 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 43 82 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 43 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 82 (accept_3_3 32 43 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 82 (Polychromatic418967fa.accept_7_3_1_5_1_44 31
  43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 82
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 82 (accept_3_3 29 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43
  82 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 43 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 82 (accept_3_3 26 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 43 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 82 (Polychromatic418967fa.accept_7_3_1_5_1_44 24
  43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 82 (accept_3_3 23 43 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 82 (Polychromatic418967fa.accept_9_4_7_1_1_379 22
  43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 82
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 82 (accept_3_3 20 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43
  82 (Polychromatic418967fa.accept_20_19_3_2_1_3118 19 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 82 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 43 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 82 (accept_3_3 17 43 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 82 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 43 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 82
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 82 (accept_3_3 14 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43
  82 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 43 82 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 82 (accept_3_3 11 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 43 82 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 43 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 82 (accept_3_3 8 43 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 82 (Polychromatic418967fa.accept_16_7_11_2_1_3117 7
  43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 82
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 82 (accept_3_3 5 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 82
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 82 (accept_3_3 2 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 82)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 42 82
  (Eq.refl Bool.true) (allA_succ_of_gcd 40 42 82 2 20 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 42 82 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 82 2 19 21 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 82
  (Polychromatic418967fa.accept_25_12_17_7_1_3116 37 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 82 2 18 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 82 (accept_3_3 35 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 82
  2 17 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42
  82 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 42 82 2 16 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 42 82 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 42 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 82 2 15 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 82 (accept_3_3 29 42 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 82 2 14 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 42 82 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 82 2 13 21 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 82
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 82 2 12 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 82 (accept_3_3 23 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 82
  2 11 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42
  82 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 82 2 10 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 82 (Polychromatic418967fa.accept_15_4_12_7_1_3115 19 42 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 82 2 9 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 82 (accept_3_3 17 42 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 82 2 8 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 82 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 42 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 82 2 7 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 82 (Polychromatic418967fa.accept_9_4_6_1_1_393 13
  42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 82 2 6 21 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 82 (accept_3_3 11 42
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 82 2 5 21 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 82
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 82 2 4 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 82 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 42 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 82 2 3 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 82 (accept_3_3 5 42 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 82 2 2 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 82 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 42 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 82 2 1 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 82 (Polychromatic418967fa.accept_13_1_3_4_1_925 1 42
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  82))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 82 (allA_of_3_1 41 41 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 82 (allA_succ_of_accept 39 40 82 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 40 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 82 2 19 20 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 82
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 40 82 2 18 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 40 82 (accept_3_3 35 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 82
  2 17 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40
  82 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 40 82 2 16 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 40 82 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 40 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 82 2 15 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 82 (accept_3_3 29 40 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 40 82 2 14 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 40 82 (Polychromatic418967fa.accept_15_12_10_7_1_1357 27 40 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 82 2 13 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 82 (Polychromatic418967fa.accept_9_7_4_1_1_391 25
  40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 82 2 12 20 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 82 (accept_3_3 23 40
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 82 2 11 20 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 82
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 82 2 10 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 82 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 40 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 82 2 9 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 82 (accept_3_3 17 40 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 82 2 8 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 40 82 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 40 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 82 2 7 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 82 (Polychromatic418967fa.accept_12_1_4_10_1_209 13
  40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 82 2 6 20 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 82 (accept_3_3 11 40
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 82 2 5 20 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 82
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 82 2 4 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 82 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 82 2 3 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 82 (accept_3_3 5 40 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 82 2 2 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 82 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 40 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 82 2 1 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 82 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  82)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 82 (allA_succ_of_accept 38 39 82 (accept_3_3 38 39 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 39
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 82
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 82 (accept_3_3 35 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39
  82 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 39 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 82 (accept_3_3 32 39 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 39 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 82 (Polychromatic418967fa.accept_7_2_4_5_1_313 30
  39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 82 (accept_3_3 29 39 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 82 (Polychromatic418967fa.accept_15_13_9_7_1_2194
  28 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 82
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 82 (accept_3_3 26 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39
  82 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 39 82 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 39 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 82 (accept_3_3 23 39 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 39 82 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 39 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 82 (accept_3_3 20 39 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 82
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 82 (accept_3_3 17 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39
  82 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 39 82 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 39 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 82 (accept_3_3 14 39 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 39 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 82 (Polychromatic418967fa.accept_11_1_6_5_1_1732
  12 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 82 (accept_3_3 11 39
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 82
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 39 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 82 (accept_3_3 8 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 82 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 39 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 82 (accept_3_3 5 39 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 82 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 39 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 82
  (Polychromatic418967fa.accept_19_3_1_6_1_3114 3 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 39 82 (accept_3_3 2 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 82
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 39 82))))))))))))))))))))))))))))))))))))))) (allB_succ 38 82 (allA_of_3_1 38 38 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 37 82 (allA_succ_of_accept 36 37 82 (Polychromatic418967fa.accept_13_10_11_4_1_2248 36
  37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 82 (accept_3_3 35 37 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 82 (Polychromatic418967fa.accept_10_4_7_2_1_211 34
  37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 82
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 82 (accept_3_3 32 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37
  82 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 82 (Polychromatic418967fa.accept_19_11_18_6_1_3113 30 37 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 82 (accept_3_3 29 37 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 82 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 37 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 82 (accept_3_3 26 37 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 82 (Polychromatic418967fa.accept_7_4_2_5_1_527 25
  37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 82
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 82 (accept_3_3 23 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 37
  82 (Polychromatic418967fa.accept_19_3_18_6_1_3112 22 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 82 (accept_3_3 20 37 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 82
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 82 (accept_3_3 17 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 37
  82 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 37 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 82 (accept_3_3 14 37 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 37 82 (Polychromatic418967fa.accept_16_13_5_2_1_2131 13 37 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 82 (Polychromatic418967fa.accept_13_12_11_4_1_3111
  12 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 82 (accept_3_3 11 37
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 82 (Polychromatic418967fa.accept_7_3_2_5_1_147
  10 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 82
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 82 (accept_3_3 8 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 82
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 82 (Polychromatic418967fa.accept_13_6_11_4_1_938 6 37 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 82 (accept_3_3 5 37 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 82 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 37 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 82 (accept_3_3 2 37 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 82 (Polychromatic418967fa.accept_19_1_18_6_1_3110 1
  37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37
  82))))))))))))))))))))))))))))))))))))) (allB_succ 36 82 (allA_succ_of_accept 35 36 82 (accept_3_3 35 36 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 82 2 17 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 82 (Polychromatic418967fa.accept_13_7_10_4_1_919 33 36 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 82 2 16 18 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 82
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 82 2 15 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 82 (accept_3_3 29 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 82
  2 14 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36
  82 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 82 2 13 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 82 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 36 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 82 2 12 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 82 (accept_3_3 23 36 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 36 82 2 11 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 36 82 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 36 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 82 2 10 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 82 (Polychromatic418967fa.accept_11_8_3_5_1_355 19
  36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 82 2 9 18 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 82 (accept_3_3 17 36
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 82 2 8 18 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 82
  (Polychromatic418967fa.accept_25_15_11_7_1_3109 15 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 36 82 2 7 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 82 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 36 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 82 2 6 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 82 (accept_3_3 11 36 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 36 82 2 5 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 36 82 (Polychromatic418967fa.accept_19_9_17_6_1_3108 9 36 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 82 2 4 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 82 (Polychromatic418967fa.accept_13_7_10_4_1_919 7
  36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 82 2 3 18 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 82 (accept_3_3 5 36
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 82 2 2 18 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 82
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 82 2 1 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 82 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 36 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 82)))))))))))))))))))))))))))))))))))) (allB_succ 35 82 (allA_of_3_1 35
  35 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 82 (allA_succ_of_accept 33 34 82
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 82 2 16 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 82 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 34 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 82 2 15 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 82 (accept_3_3 29 34 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 34 82 2 14 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 34 82 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 34 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 82 2 13 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 82 (Polychromatic418967fa.accept_7_4_6_5_1_141 25
  34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 82 2 12 17 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 82 (accept_3_3 23 34
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 82 2 11 17 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 82
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 82 2 10 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 82 (Polychromatic418967fa.accept_18_1_16_10_1_2065 19 34 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 82 2 9 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 82 (accept_3_3 17 34 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 82 2 8 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 82 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 34 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 82 2 7 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 82 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 82 2 6 17 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 82 (accept_3_3 11 34
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 82 2 5 17 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 82
  (Polychromatic418967fa.accept_13_9_8_4_1_937 9 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 82 2 4 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 82 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 34 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 82 2 3 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 82 (accept_3_3 5 34 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 82 2 2 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 82 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 34 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 82 2 1 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 82 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 34
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 82))))))))))))))))))))))))))))))))))
  (allB_succ 33 82 (allA_succ_of_accept 32 33 82 (accept_3_3 32 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 33 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 82 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 33 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 82 (accept_3_3 29 33 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 82 (Polychromatic418967fa.accept_16_12_1_2_1_2163
  28 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 82
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 82 (accept_3_3 26 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33
  82 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 33 82 (Polychromatic418967fa.accept_13_11_7_4_1_1561 24 33 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 82 (accept_3_3 23 33 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 33 82 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 33 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 82 (Polychromatic418967fa.accept_9_3_6_1_1_24 21
  33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 82 (accept_3_3 20 33 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 82
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 82 (accept_3_3 17 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33
  82 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 33 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 82 (accept_3_3 14 33 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 33 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 82 (Polychromatic418967fa.accept_9_3_6_1_1_24 12
  33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 82 (accept_3_3 11 33 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 82 (Polychromatic418967fa.accept_13_10_7_4_1_2262
  10 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 82
  (Polychromatic418967fa.accept_13_9_7_4_1_953 9 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 82 (accept_3_3 8 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 82
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 82 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 33 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 82 (accept_3_3 5 33 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 82 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 33 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 82 (accept_3_3 2 33 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 82)))))))))))))))))))))))))))))))))
  (allB_succ 32 82 (allA_of_3_1 32 32 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 82 (allA_succ_of_accept
  30 31 82 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 31 82 (accept_3_3 29 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 31 82 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 31 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 82 (accept_3_3 26 31 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 82
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 82 (accept_3_3 23 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31
  82 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 31 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 82 (accept_3_3 20 31 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 31 82 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 31 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 82 (Polychromatic418967fa.accept_11_7_9_5_1_338 18
  31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 82 (accept_3_3 17 31 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 82 (Polychromatic418967fa.accept_7_2_3_5_1_34 16
  31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 82
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 82 (accept_3_3 14 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31
  82 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 31 82 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 31 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 82 (accept_3_3 11 31 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 31 82 (Polychromatic418967fa.accept_13_10_5_4_1_3107 10 31 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 82 (accept_3_3 8 31 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 82 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 31
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 82
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 82 (accept_3_3 5 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 82
  (Polychromatic418967fa.accept_12_4_7_10_1_563 4 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 82 (accept_3_3 2 31 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 82))))))))))))))))))))))))))))))) (allB_succ 30 82
  (allA_succ_of_accept 29 30 82 (accept_3_3 29 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 82
  2 14 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 30
  82 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 30 82 2 13 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 30 82 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 30 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 82 2 12 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 82 (accept_3_3 23 30 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 30 82 2 11 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 30 82 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 30 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 82 2 10 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 82 (Polychromatic418967fa.accept_22_19_8_16_1_3106
  19 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 82 2 9 15 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 82 (accept_3_3 17 30
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 82 2 8 15 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 82
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 30 82 2 7 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 30 82 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 30 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 82 2 6 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 82 (accept_3_3 11 30 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 30 82 2 5 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 30 82 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 30 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 82 2 4 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 82 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 30
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 82 2 3 15 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 82 (accept_3_3 5 30
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 82 2 2 15 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 82
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 30 82 2 1 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 82 (Polychromatic418967fa.accept_17_1_13_14_1_478 1 30 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 82)))))))))))))))))))))))))))))) (allB_succ 29 82 (allA_of_3_1 29 29 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 82 (allA_succ_of_accept 27 28 82
  (Polychromatic418967fa.accept_34_27_28_14_1_3105 27 28 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 82 2 13 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 82 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 28 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 82 2 12 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 82 (accept_3_3 23 28 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 28 82 2 11 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 28 82 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 28 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 82 2 10 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 82 (Polychromatic418967fa.accept_12_7_4_10_1_572 19
  28 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 82 2 9 14 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 82 (accept_3_3 17 28
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 82 2 8 14 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 28 82
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 28 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 28 82 2 7 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 28 82 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 28 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 82 2 6 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 82 (accept_3_3 11 28 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 28 82 2 5 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 28 82 (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 28 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 82 2 4 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 82 (Polychromatic418967fa.accept_12_7_4_10_1_572 7
  28 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 82 2 3 14 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 82 (accept_3_3 5 28
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 82 2 2 14 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 82
  (Polychromatic418967fa.accept_17_3_11_14_1_2071 3 28 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 82 2 1 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 82 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 28 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 82)))))))))))))))))))))))))))) (allB_succ 27 82 (allA_succ_of_accept 26
  27 82 (accept_3_3 26 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 82
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 27 82 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 27 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 82 (accept_3_3 23 27 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 27 82 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 27 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 82 (accept_3_3 20 27 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 82
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 82 (accept_3_3 17 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27
  82 (Polychromatic418967fa.accept_13_3_1_4_1_945 16 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 27 82 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 27 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 82 (accept_3_3 14 27 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 27 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 82 (Polychromatic418967fa.accept_18_12_9_10_1_3104
  12 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 82 (accept_3_3 11 27
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 82
  (Polychromatic418967fa.accept_13_10_1_4_1_3103 10 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 27 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 82 (accept_3_3 8 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 82 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 27 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 82 (accept_3_3 5 27 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 82 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 27 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 82
  (Polychromatic418967fa.accept_13_3_1_4_1_945 3 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 82 (accept_3_3 2 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 82
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 82))))))))))))))))))))))))))) (allB_succ 26 82 (allA_of_3_1 26 26 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 25 82 (allA_succ_of_accept 24 25 82 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 25 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 82 (accept_3_3 23 25 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 82 (Polychromatic418967fa.accept_7_1_4_5_1_35 22
  25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 82
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 82 (accept_3_3 20 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25
  82 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 82 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 25 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 82 (accept_3_3 17 25 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 82 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 25 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 82 (accept_3_3 14 25 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 82 (Polychromatic418967fa.accept_7_6_4_5_1_314 13
  25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 82
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 82 (accept_3_3 11 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 25
  82 (Polychromatic418967fa.accept_20_10_5_2_1_3102 10 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 82 (accept_3_3 8 25 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 25 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 82 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 25
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 82 (accept_3_3 5 25 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 82 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 25
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 82
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 82 (accept_3_3 2 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 82
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 82))))))))))))))))))))))))) (allB_succ 24 82 (allA_succ_of_accept 23 24 82 (accept_3_3 23 24 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 82 2 11 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 82 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 24 82 2 10 12 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 82
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 24 82 2 9 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 24 82 (accept_3_3 17 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 82
  2 8 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24
  82 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 24 82 2 7 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 82 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 24 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 82 2 6 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 82 (accept_3_3 11 24 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 24 82 2 5 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 24 82 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 24 82 2 4 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 82 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 82 2 3 12 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 82 (accept_3_3 5 24
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 82 2 2 12 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 24 82
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 24 82 2 1 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 24 82 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 24 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 82)))))))))))))))))))))))) (allB_succ 23 82 (allA_of_3_1 23 23 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 82 (allA_succ_of_accept 21 22 82
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 22 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 82 2 10 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 82 (Polychromatic418967fa.accept_13_6_9_4_1_2288 19 22 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 82 2 9 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 82 (accept_3_3 17 22 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 82 2 8 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 82 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 22 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 82 2 7 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 82 (Polychromatic418967fa.accept_7_6_1_5_1_322 13
  22 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 82 2 6 11 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 82 (accept_3_3 11 22
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 82 2 5 11 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 82
  (Polychromatic418967fa.accept_16_9_6_2_1_3101 9 22 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 82 2 4 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 82 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 22 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 82 2 3 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 82 (accept_3_3 5 22 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 82 2 2 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 82 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 22 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 82 2 1 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 82 (Polychromatic418967fa.accept_16_1_6_2_1_3100 1
  22 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 82)))))))))))))))))))))) (allB_succ 21
  82 (allA_succ_of_accept 20 21 82 (accept_3_3 20 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  21 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 21 82 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 21 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 82 (accept_3_3 17 21 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 82 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 21 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 82 (accept_3_3 14 21 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 82
  (Polychromatic418967fa.accept_13_12_8_4_1_3099 12 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 82 (accept_3_3 11 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21
  82 (Polychromatic418967fa.accept_13_10_8_4_1_3098 10 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 82 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 21 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 82 (accept_3_3 8 21 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 21 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 82 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 21
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 82 (accept_3_3 5 21 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 82 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 21
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 82
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 82 (accept_3_3 2 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 82
  (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 82))))))))))))))))))))) (allB_succ 20 82 (allA_of_3_1 20 20 82 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 19 82 (allA_succ_of_accept 18 19 82 (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 19 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 82 (accept_3_3 17 19 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 82 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 19 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 82
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 19 82 (accept_3_3 14 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19
  82 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 19 82 (Polychromatic418967fa.accept_15_12_4_7_1_3097 12 19 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 82 (accept_3_3 11 19 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 19 82 (Polychromatic418967fa.accept_13_10_6_4_1_1583 10 19 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 82 (accept_3_3 8 19 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 82 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7
  19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 82
  (Polychromatic418967fa.accept_16_6_3_2_1_3096 6 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 82 (accept_3_3 5 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 82
  (Polychromatic418967fa.accept_12_4_7_10_1_563 4 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 82 (accept_3_3 2 19 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 82))))))))))))))))))) (allB_succ 18 82 (allA_succ_of_accept 17
  18 82 (accept_3_3 17 18 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 82 2 8 9 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 82
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 18 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 82 2 7 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 82 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 18 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 82 2 6 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 82 (accept_3_3 11 18 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 82 2 5 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 82 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 18 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 82 2 4 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 82 (Polychromatic418967fa.accept_19_7_18_6_1_3095 7
  18 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 82 2 3 9 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 82 (accept_3_3 5 18
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 82 2 2 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 82 (Polychromatic418967fa.accept_12_3_6_10_1_576 3
  18 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 18 82 2 1 9 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 82
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 18 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 82)))))))))))))))))) (allB_succ 17 82 (allA_of_3_1 17 17 82 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 16 82 (allA_succ_of_accept 15 16 82 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 16 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 16 82 2 7 8 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 16 82
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 16 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 16 82 2 6 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 16 82 (accept_3_3 11 16 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 16 82
  2 5 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 16 82
  (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 16 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 16 82 2 4 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 16 82 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 16 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 82 2 3 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 82 (accept_3_3 5 16 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 16 82 2 2 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 16 82 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 16 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 16 82 2 1 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 16 82 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 16
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 82)))))))))))))))) (allB_succ 15 82
  (allA_succ_of_accept 14 15 82 (accept_3_3 14 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15
  82 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 82 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 15 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 82 (accept_3_3 11 15 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 82 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 15 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 82 (accept_3_3 8 15 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 82
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 82 (accept_3_3 5 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 82
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 82 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 82 (accept_3_3 2 15 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 82))))))))))))))) (allB_succ 14 82 (allA_of_3_1 14 14 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 82 (allA_succ_of_accept 12 13 82
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 82 (accept_3_3 11 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13
  82 (Polychromatic418967fa.accept_17_10_13_14_1_3094 10 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 82 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 82 (accept_3_3 8 13 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 13 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 82 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 13
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 82 (accept_3_3 5 13 82
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 82 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 13
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 82
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 82 (accept_3_3 2 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 82
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 82))))))))))))) (allB_succ 12 82 (allA_succ_of_accept 11 12 82 (accept_3_3 11 12 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 82 2 5 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 12 82 (Polychromatic418967fa.accept_16_9_12_2_1_3093 9 12 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 82 2 4 6 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 82
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 12 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 82 2 3 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 82 (accept_3_3 5 12 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 82 2
  2 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 82
  (Polychromatic418967fa.accept_13_3_12_4_1_110 3 12 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 12 82 2 1 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 12 82 (Polychromatic418967fa.accept_16_1_12_2_1_2136 1 12 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 82)))))))))))) (allB_succ 11 82 (allA_of_3_1 11 11 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 10 82 (allA_succ_of_accept 9 10 82 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 10 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 82 2 4 5 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 82
  (Polychromatic418967fa.accept_13_7_10_4_1_919 7 10 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 82 2 3 5 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 82 (accept_3_3 5 10 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 82 2
  2 5 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 82
  (Polychromatic418967fa.accept_15_3_10_7_1_2196 3 10 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 82 2 1 5 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 82 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 10 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 82)))))))))) (allB_succ 9 82 (allA_succ_of_accept 8 9 82 (accept_3_3 8 9
  82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 82
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 9 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 82 (accept_3_3 5 9 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 82
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 9 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 82 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 82 (accept_3_3 2 9 82 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 82 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 9 82))))))))) (allB_succ 8 82 (allA_of_3_1 8 8 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 7 82 (allA_succ_of_accept 6 7 82 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 7 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 7 82 (accept_3_3 5 7 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 82 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 7 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 7 82
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 7 82 (accept_3_3 2 7 82 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 82
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 7 82))))))) (allB_succ 6 82 (allA_succ_of_accept 5 6 82 (accept_3_3 5 6 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 6 82 2 2 3 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 6 82 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 6 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 6 82 2 1 3 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 82 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 6 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 82)))))) (allB_succ 5 82 (allA_of_3_1 5 5 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 82 (allA_succ_of_accept 3 4 82 (Polychromatic418967fa.accept_9_3_4_1_1_22
  3 4 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 82 2 1 2 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 82
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 4 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 82)))) (allB_succ 3 82 (allA_succ_of_accept 2 3 82 (accept_3_3 2 3 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 82 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 82))) (allB_succ 2 82 (allA_of_3_1 2 2 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_two 82))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


